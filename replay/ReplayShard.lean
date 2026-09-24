import Lean
open Lean

/-! # Lane I — layered-shard kernel replay (for final-assembly closures too large for one process)

usage:
  plan : lean --run ReplayShard.lean --plan OUT_PREFIX [--max-consts N] [--max-mods M] Root1 [Root2 ...]
         writes OUT_PREFIX.tsv (one shard per line: `id <TAB> height <TAB> m1,m2,...`) and OUT_PREFIX.summary
  shard: lean --run ReplayShard.lean --shard OUT_PREFIX.tsv K [--axioms D1,D2,...]
  (LEAN_PATH identical for the plan and for every shard.)

Height of a target module = 0 if it imports only trusted modules (Init, Lean, Std, Lake, Mathlib, Batteries, Aesop,
Qq, ProofWidgets, Plausible, ImportGraph, LeanSearchClient), else 1 + max height of its target imports. A shard is a
set of target modules of ONE height. Shard run: import (trust level 0) the union of the direct imports of the shard's
modules — none of the shard's modules can be in that closure, because every import has strictly smaller height (this
is also checked) — then send every constant of every shard module through the kernel (`Environment.replay`).
Soundness of the whole: every target module is replayed in exactly one shard against the constants of its imports as
stored in the same olean files (fixed LEAN_PATH); by induction on height every constant of the closure is kernel-checked
relative to kernel-checked dependencies. The driver (tools/replay_sharded.py) checks the coverage and all results.
-/

def trustedRoots : List String :=
  ["Init", "Lean", "Std", "Lake", "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets",
   "Plausible", "ImportGraph", "LeanSearchClient"]

def isTrusted (m : Name) : Bool := trustedRoots.contains m.getRoot.toString

/-- Axioms reachable from `n` in `kenv`. -/
def collectAxioms (kenv : Kernel.Environment) (n : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[n]
  let mut axs : Array Name := #[]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    match kenv.find? c with
    | some ci =>
      if ci matches .axiomInfo _ then axs := axs.push c
      for u in ci.getUsedConstantsAsSet do
        if !visited.contains u then stack := stack.push u
    | none => axs := axs.push (Name.mkStr c "<MISSING>")
  return axs.qsort (fun a b => a.toString < b.toString)

unsafe def planMode (roots : Array Name) (outPrefix : String) (maxConsts maxMods : Nat) : IO UInt32 := do
  let mut imps : Std.HashMap Name (Array Name) := {}
  let mut nconst : Std.HashMap Name Nat := {}
  let mut order : Array Name := #[]
  let mut done : NameSet := {}
  let mut visiting : NameSet := {}
  let mut stack : Array (Name × Bool) := roots.reverse.map (·, false)
  while !stack.isEmpty do
    let (m, expanded) := stack.back!
    stack := stack.pop
    if done.contains m then continue
    if expanded then
      done := done.insert m
      order := order.push m
      continue
    if isTrusted m || visiting.contains m then continue
    visiting := visiting.insert m
    let p ← findOLean m
    unless (← p.pathExists) do throw <| IO.userError s!"missing olean {p} for {m}"
    let (md, _region) ← readModuleData p
    let ti := (md.imports.map (·.module)).filter (fun i => !isTrusted i)
    imps := imps.insert m ti
    nconst := nconst.insert m md.constants.size
    stack := stack.push (m, true)
    for i in ti.reverse do
      if !done.contains i then stack := stack.push (i, false)
  let mut height : Std.HashMap Name Nat := {}
  let mut maxH := 0
  for m in order do
    let h := (imps[m]!).foldl (fun acc i => max acc (height[i]! + 1)) 0
    height := height.insert m h
    maxH := max maxH h
  -- shards: per height, chunks bounded by maxConsts constants and maxMods modules
  let mut lines : Array String := #[]
  let mut sid := 0
  let mut totalConsts := 0
  for h in [0:maxH+1] do
    let layer := order.filter (fun m => height[m]! == h)
    let mut cur : Array Name := #[]
    let mut curC := 0
    for m in layer do
      let c := nconst[m]!
      totalConsts := totalConsts + c
      if !cur.isEmpty && (curC + c > maxConsts || cur.size ≥ maxMods) then
        lines := lines.push s!"{sid}\t{h}\t{",".intercalate (cur.toList.map toString)}"
        sid := sid + 1
        cur := #[]
        curC := 0
      cur := cur.push m
      curC := curC + c
    if !cur.isEmpty then
      lines := lines.push s!"{sid}\t{h}\t{",".intercalate (cur.toList.map toString)}"
      sid := sid + 1
  IO.FS.writeFile (outPrefix ++ ".tsv") ("\n".intercalate lines.toList ++ "\n")
  let summary := s!"roots={roots.toList} target_modules={order.size} target_constants={totalConsts} heights={maxH+1} shards={sid} max_consts={maxConsts} max_mods={maxMods}\n"
  IO.FS.writeFile (outPrefix ++ ".summary") summary
  IO.print summary
  return 0

unsafe def shardMode (planPath : String) (k : Nat) (axiomsOf : Array Name) : IO UInt32 := do
  let content ← IO.FS.readFile planPath
  let some line := (content.splitOn "\n").find? (fun l => l.startsWith s!"{k}\t")
    | IO.println s!"SHARD_NOT_FOUND {k}"; return 2
  let parts := line.splitOn "\t"
  let mods : Array Name := ((parts[2]!).splitOn ",").toArray.filter (· ≠ "") |>.map String.toName
  let modSet : NameSet := mods.foldl (fun s n => s.insert n) {}
  let t0 ← IO.monoMsNow
  let mut data : Array (Name × ModuleData × System.FilePath) := #[]
  let mut base : Array Import := #[]
  let mut baseSet : NameSet := {}
  let mut nConsts := 0
  for m in mods do
    let p ← findOLean m
    let (md, _region) ← readModuleData p
    data := data.push (m, md, p)
    nConsts := nConsts + md.constants.size
    for i in md.imports do
      if modSet.contains i.module then
        IO.println s!"SHARD_INVALID {m} imports {i.module} of the same shard"; return 1
      if !baseSet.contains i.module then
        baseSet := baseSet.insert i.module
        base := base.push { module := i.module }
  let env ← importModules base {} (trustLevel := 0)
  let t1 ← IO.monoMsNow
  for n in env.header.moduleNames do
    if modSet.contains n then
      IO.println s!"SHARD_INVALID {n} is already in the imported base environment"; return 1
  IO.println s!"SHARD {k} height={parts[1]!} modules={mods.size} constants={nConsts} base_imports={base.size} base_modules={env.header.moduleNames.size} import_ms={t1 - t0}"
  (← IO.getStdout).flush
  let mut env := env
  for (m, md, p) in data do
    let mut newConsts : Std.HashMap Name ConstantInfo := {}
    for ci in md.constants do
      newConsts := newConsts.insert ci.name ci
    let s ← IO.monoMsNow
    try
      env ← env.replay newConsts
    catch e =>
      IO.println s!"REPLAY_FAIL shard={k} module={m} path={p}\n{e}"
      return 1
    let e ← IO.monoMsNow
    IO.println s!"MOD {m} consts={md.constants.size} ms={e - s}"
    (← IO.getStdout).flush
  let kenv := env.toKernelEnv
  for d in axiomsOf do
    if (kenv.find? d).isSome then
      let axs := collectAxioms kenv d
      IO.println s!"'{d}' depends on axioms: [{", ".intercalate (axs.toList.map toString)}]"
  let t2 ← IO.monoMsNow
  IO.println s!"SHARD_REPLAY_OK {k} modules={mods.size} constants={nConsts} replay_ms={t2 - t1}"
  return 0

partial def argVal (args : List String) (flag : String) : Option String :=
  match args with
  | [] => none
  | a :: b :: rest => if a == flag then some b else argVal (b :: rest) flag
  | _ => none

unsafe def main (argv : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let axiomsOf : Array Name :=
    ((argVal argv "--axioms").getD "" |>.splitOn ",").toArray.filter (· ≠ "") |>.map String.toName
  if let some outPrefix := argVal argv "--plan" then
    let maxC := ((argVal argv "--max-consts").bind String.toNat?).getD 20000
    let maxM := ((argVal argv "--max-mods").bind String.toNat?).getD 400
    let flagVals := [outPrefix, (argVal argv "--max-consts").getD "", (argVal argv "--max-mods").getD ""]
    let roots := argv.filter (fun a => !a.startsWith "--" && !flagVals.contains a)
    return ← planMode (roots.toArray.map String.toName) outPrefix maxC maxM
  match argv with
  | "--shard" :: plan :: k :: _ =>
    match k.toNat? with
    | some kk => shardMode plan kk axiomsOf
    | none => IO.println "bad shard index"; return 2
  | _ =>
    IO.println "usage: --plan OUT_PREFIX [--max-consts N] [--max-mods M] Roots... | --shard PLAN.tsv K [--axioms D1,..]"
    return 2

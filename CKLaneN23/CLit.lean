import CKLaneN23.CQ

/-!
# CKLaneN23.CLit — fast certificate literals (Lane N23b)

`n23lit NAME "tokens"` adds `NAME : TMd` whose value is built directly as an `Expr` (explicit
constructors, raw numerals, rationals as `qq n d`), bypassing term elaboration (which is quadratic on
large nested list literals).  The declaration is type-checked by the kernel like any definition; this
is only a faster way to write down certificate data (no axioms, no trust change).

Token format (whitespace separated integers):
  TM    := nS SLOT^nS  rnum rden  n
  SLOT  := nM (i k nL (e num den)^nL)^nM          -- one `QPoly` (x-coefficient)
-/

namespace CKLaneN23.CT

open Lean Elab Command Meta

private def zE (v : Int) : Expr :=
  if v ≥ 0 then mkApp (mkConst ``Int.ofNat) (mkRawNatLit v.toNat)
  else mkApp (mkConst ``Int.negSucc) (mkRawNatLit ((-v) - 1).toNat)

private def qE (num : Int) (den : Nat) : Expr :=
  mkApp2 (mkConst ``CKLaneN23.CT.qq) (zE num) (mkRawNatLit den)

private def listE (ty : Expr) (xs : Array Expr) : Expr := Id.run do
  let mut acc := mkApp (mkConst ``List.nil [Level.zero]) ty
  for x in xs.reverse do
    acc := mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc
  return acc

private def prodE (a b : Expr) (x y : Expr) : Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) a b x y

private def prodT (a b : Expr) : Expr := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b

private structure PS where
  toks : Array Int
  pos : Nat

private def next (s : PS) : Except String (Int × PS) :=
  if h : s.pos < s.toks.size then .ok (s.toks[s.pos], { s with pos := s.pos + 1 })
  else .error "n23lit: unexpected end of tokens"

private def parseTM (toks : Array Int) : Except String Expr := do
  let tZ := mkConst ``Int
  let tQ := mkConst ``Rat
  let tN := mkConst ``Nat
  let tL := prodT tZ tQ                      -- ℤ × ℚ
  let tLP := mkApp (mkConst ``List [Level.zero]) tL
  let tK := prodT tN tN
  let tM := prodT tK tLP                     -- (ℕ × ℕ) × LPoly
  let tQP := mkApp (mkConst ``List [Level.zero]) tM
  let mut s : PS := ⟨toks, 0⟩
  let (nS, s1) ← next s; s := s1
  let mut slots : Array Expr := #[]
  for _ in [0:nS.toNat] do
    let (nM, s2) ← next s; s := s2
    let mut mons : Array Expr := #[]
    for _ in [0:nM.toNat] do
      let (i, s3) ← next s; s := s3
      let (k, s4) ← next s; s := s4
      let (nL, s5) ← next s; s := s5
      let mut terms : Array Expr := #[]
      for _ in [0:nL.toNat] do
        let (e, s6) ← next s; s := s6
        let (num, s7) ← next s; s := s7
        let (den, s8) ← next s; s := s8
        terms := terms.push (prodE tZ tQ (zE e) (qE num den.toNat))
      let key := prodE tN tN (mkRawNatLit i.toNat) (mkRawNatLit k.toNat)
      mons := mons.push (prodE tK tLP key (listE tL terms))
    slots := slots.push (listE tM mons)
  let (rn, s9) ← next s; s := s9
  let (rd, s10) ← next s; s := s10
  let (n, s11) ← next s; s := s11
  if s.pos != toks.size then throw "n23lit: trailing tokens"
  let P := listE tQP slots
  return mkApp3 (mkConst ``CKLaneN23.CT.TMd.mk) P (qE rn rd.toNat) (mkRawNatLit n.toNat)

/-- whitespace-separated integers (optional leading `-`) -/
private def tokenize (cs : List Char) : Except String (Array Int) := Id.run do
  let mut out : Array Int := #[]
  let mut cur : Nat := 0
  let mut neg : Bool := false
  let mut inTok : Bool := false
  for c in cs do
    if c == ' ' || c == '\n' || c == '\t' || c == '\r' then
      if inTok then
        out := out.push (if neg then -(cur : Int) else (cur : Int))
        cur := 0; neg := false; inTok := false
    else if c == '-' then
      if inTok then return .error "n23lit: misplaced '-'"
      neg := true; inTok := true
    else if c.isDigit then
      cur := cur * 10 + (c.toNat - '0'.toNat); inTok := true
    else
      return .error s!"n23lit: bad character {c}"
  if inTok then
    out := out.push (if neg then -(cur : Int) else (cur : Int))
  return .ok out

/-- `n23lit NAME "tokens"` : add the certificate literal `NAME : TMd`. -/
elab "n23lit " id:ident str:str : command => do
  let toks ← match tokenize str.getString.toList with
    | .ok t => pure t
    | .error e => throwError e
  match parseTM toks with
  | .error e => throwError e
  | .ok val =>
    let ns ← getCurrNamespace
    let name := ns ++ id.getId
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := name, levelParams := [], type := mkConst ``CKLaneN23.CT.TMd, value := val,
        hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }

end CKLaneN23.CT

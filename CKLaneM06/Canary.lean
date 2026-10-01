import CKLaneM06.Checker

/-!
# Lane M06 canary: hardest archived `parent_tail` leaf

Archived same-side leaf `4444444444444444513` (`hardest_14_witnesses.json` id 8, owner `parent_tail`,
archived lower enclosure `0.0021591948207279167`, the smallest of the 24 `parent_tail` leaves):
exact box `x ∈ [16,32]`, `b ∈ [17/64,1/2]`, `t ∈ [1/131072,1/65536]`.

`canary_dominance` : for every law in the exact box, `psi ≤ phi` at the parent.
`canary_owner`     : the psi-branch owner statement on the box (vacuous by dominance).
Negative controls (kernel-evaluated to `false`): perturbed eta witness `u`, perturbed entropy
rounding point `Ehi`, and a wrong box (last path digit flipped, `b ∈ [1/32,17/64]`).
-/

set_option autoImplicit false

namespace CKLaneM06.Canary

open CKLaneM06

/-- Archived path `4444444444444444513` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 4294967296 : ℚ), rhi := (1 / 65536 : ℚ),
    Ehi := (1073892907 / 140737488355328 : ℚ), u := (15873933679 / 549755813888 : ℚ) }

/-- The path recursion reproduces the archived box exactly. -/
theorem box_eq : pathBox path = ⟨16, 32, 17 / 64, 1 / 2, 1 / 131072, 1 / 65536⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

/-- **Canary.** Parent dominance on the exact archived box. -/
theorem canary_dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

/-- **Canary (owner form).** -/
theorem canary_owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

/-! ## Negative controls -/

/-- Perturbed eta witness (`u + 1/1000`). -/
def witBadU : Witness := { wit with u := (15873933679 / 549755813888 : ℚ) + 1 / 1000 }

/-- Perturbed entropy rounding point (`Ehi / 2`). -/
def witBadE : Witness := { wit with Ehi := (1073892907 / 281474976710656 : ℚ) }

/-- Wrong box: last archived digit flipped (`...512`, i.e. `b ∈ [1/32, 17/64]`). -/
def pathBad : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2]

theorem reject_badU : checkLeaf path witBadU = false := by decide +kernel

theorem reject_badE : checkLeaf path witBadE = false := by decide +kernel

theorem reject_badBox : checkLeaf pathBad wit = false := by decide +kernel

end CKLaneM06.Canary

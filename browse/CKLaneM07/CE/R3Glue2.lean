import CKLaneN1.R3Q
import CKLaneM07.CE.R3Glue

/-!
# Lane M07 / CE-stat row 3: mixed leaf predicate for the numeric cover

`leaf21 B w := leafOK2 B w || leafOK B w` — N1's sharpened checker `leafOK2` (CKLaneN1.R3Q) first, then
the original `leafOK` (retVac || tcVac || M07 `r3BoxOK`); both are sound into the same `CKLaneN1.R3.Sem`.
`sem_of_tree21` is the tree version (N1 `PT.cover`).  The order only matters for kernel cost: most leaves
of the octaves k ≤ 15 pass `leafOK2`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE.R3Glue

open CKLaneN1

def leaf21 (B : B3) (w : CKLaneM07.CE.R3.RWit) : Bool :=
  CKLaneN1.R3.leafOK2 B w || CKLaneN1.R3.leafOK B w

theorem leaf21_sound {B : B3} {w : CKLaneM07.CE.R3.RWit} (h : leaf21 B w = true) :
    CKLaneN1.R3.Sem B := by
  simp only [leaf21, Bool.or_eq_true] at h
  rcases h with h | h
  · exact CKLaneN1.R3.leafOK2_sound h
  · exact CKLaneN1.R3.leafOK_sound h

theorem sem_of_tree21 (R : B3) (T : PT CKLaneM07.CE.R3.RWit)
    (h : T.allLeaves (fun p w => leaf21 (R.ofPath p) w) = true) : CKLaneN1.R3.Sem R := by
  intro a z y hm
  obtain ⟨q, hq, hmq⟩ := PT.cover R T hm
  exact leaf21_sound (PT.allLeaves_sound h q hq) a z y hmq

end CKLaneM07.CE.R3Glue

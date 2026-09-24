import CKLaneM07.Checker
import CKLaneG3.SCover

/-!
# Lane M07 → canonical (S) cover adapter (`CKLaneG3.SCover`, BRIEF §7)

`CKLaneM07.SBox ⟨x1,x2,b1,b2,t1,t2⟩` is the canonical `CKLaneG3.SBox ⟨x0,x1,b0,b1,t0,t1⟩` with renamed
fields; `toG` is the field-for-field map.  It commutes with the root and the halving step, hence
`toG (ssBox p) = CKLaneG3.sBox p` (`CKLaneG3.sBox_of_commute`); `CKLaneG3.InS (toG B)` is definitionally
`InSBox B`, and `SemSBox B` is literally `CKLaneG3.OwnerS (toG B)`, so `CKLaneG3.sLeafOK_of_ownerS` applies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM07

/-- Field-for-field map to the canonical box. -/
def toG (B : SBox) : CKLaneG3.SBox := ⟨B.x1, B.x2, B.b1, B.b2, B.t1, B.t2⟩

theorem toG_root : toG ssRoot = CKLaneG3.sRoot := rfl

theorem toG_step (B : SBox) (d : ℕ) : toG (ssStep B d) = CKLaneG3.sStep (toG B) d := by
  rcases d with _ | _ | _ | _ | _ | _ | d
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have e : d + 1 + 1 + 1 + 1 + 1 + 1 = d + 6 := by ring
    simp only [e, ssStep, CKLaneG3.sStep]

theorem toG_ssBox (p : List ℕ) : toG (ssBox p) = CKLaneG3.sBox p :=
  CKLaneG3.sBox_of_commute ssStep ssRoot toG toG_root toG_step p

theorem inS_toG_iff (B : SBox) (a b E : ℝ) : CKLaneG3.InS (toG B) a b E ↔ InSBox B a b E := Iff.rfl

theorem ownerS_of_semSBox {B : SBox} (h : SemSBox B) : CKLaneG3.OwnerS (toG B) :=
  fun k μ hab hin hact => h k μ hab hin hact

/-- Per-leaf adapter: the M07 semantic statement on `ssBox p` gives the `SS_Compact` obligation on the
canonical box `CKLaneG3.sBox p`. -/
theorem sLeafOK_of_semSBox {p : List ℕ} (h : SemSBox (ssBox p)) : CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  rw [← toG_ssBox]
  exact CKLaneG3.sLeafOK_of_ownerS (ownerS_of_semSBox h)

/-- Checker form: a checked witness for path `p` proves the canonical per-leaf obligation. -/
theorem sLeafOK_of_checkLeaf {p : List ℕ} {w : Wit} (h : checkLeaf p w = true) :
    CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  sLeafOK_of_semSBox (checkLeaf_sound h)

end CKLaneM07

#check @CKLaneM07.toG_ssBox
#check @CKLaneM07.sLeafOK_of_semSBox
#check @CKLaneM07.sLeafOK_of_checkLeaf
#print axioms CKLaneM07.toG_ssBox
#print axioms CKLaneM07.sLeafOK_of_semSBox
#print axioms CKLaneM07.sLeafOK_of_checkLeaf

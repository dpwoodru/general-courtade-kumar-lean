import CKLaneM1.MLChecker
import CKLaneG3.SCover

/-!
# Lane M1 → canonical (S) cover `CKLaneG3.SCover` (BRIEF §7)

`SSBox`/`ssRoot`/`ssStep`/`ssBox`/`InSS` are field-for-field the canonical `SBox`/`sRoot`/`sStep`/`sBox`/`InS`.
`toSBox_ssBox` transports the box recursion (`CKLaneG3.sBox_of_commute`); `SemSS` is definitionally
`CKLaneG3.OwnerStrictS`, closed at `a = b` by `CKLaneG3.sLeafOK_of_ownerStrictS`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM1.ML

open GeneralCK

/-- Field-for-field map to the canonical (S) box. -/
def toSBox (B : SSBox) : CKLaneG3.SBox := ⟨B.x0, B.x1, B.b0, B.b1, B.t0, B.t1⟩

theorem toSBox_step (X : SSBox) (d : ℕ) : toSBox (ssStep X d) = CKLaneG3.sStep (toSBox X) d := by
  rcases d with _ | _ | _ | _ | _ | _ | d <;> rfl

theorem toSBox_ssBox (p : List ℕ) : toSBox (ssBox p) = CKLaneG3.sBox p :=
  CKLaneG3.sBox_of_commute ssStep ssRoot toSBox rfl toSBox_step p

theorem inS_toSBox (B : SSBox) (a b E : ℝ) : CKLaneG3.InS (toSBox B) a b E ↔ InSS B a b E :=
  Iff.rfl

theorem ownerStrictS_of_semSS {B : SSBox} (h : SemSS B) : CKLaneG3.OwnerStrictS (toSBox B) := h

theorem sLeafOK_of_semSS {p : List ℕ} (h : SemSS (ssBox p)) : CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  rw [← toSBox_ssBox]
  exact CKLaneG3.sLeafOK_of_ownerStrictS (ownerStrictS_of_semSS h)

/-- Checker soundness in the coordinator's final (S) form. -/
theorem checkLeaf_sLeafOK {p : List ℕ} {w : LeafCert} (h : checkLeaf p w = true) :
    CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  sLeafOK_of_semSS (checkLeaf_sound h)

end CKLaneM1.ML

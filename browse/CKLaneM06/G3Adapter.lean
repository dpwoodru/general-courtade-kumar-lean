import CKLaneM06.CanaryS
import CKLaneG3.SCover

/-!
# Lane M06 → canonical (S) cover `CKLaneG3.SCover` adapter

`CKLaneG3.{SBox, sRoot, sStep, sBox, InS}` are field-for-field identical to the lane-local
`CKLaneM06.{SBox, sRoot, sStep, sBox, InS}` (BRIEF §7).  `toG3` renames the structure; the box
recursions agree by `CKLaneG3.sBox_of_commute`, and `InS` agrees definitionally.  Parent dominance
then gives the `SS_Compact` per-leaf obligation `CKLaneG3.SLeafOK` through `CKLaneG3.sLeafOK_of_parentS`.
-/

set_option autoImplicit false

namespace CKLaneM06

/-- Structure renaming to the canonical box type. -/
def SBox.toG3 (B : SBox) : CKLaneG3.SBox := ⟨B.x0, B.x1, B.b0, B.b1, B.t0, B.t1⟩

theorem toG3_sStep (B : SBox) (d : ℕ) : (sStep B d).toG3 = CKLaneG3.sStep B.toG3 d := by
  rcases d with _ | _ | _ | _ | _ | _ | d <;> rfl

/-- The lane-local box recursion is the canonical one. -/
theorem toG3_sBox (p : List ℕ) : (sBox p).toG3 = CKLaneG3.sBox p :=
  CKLaneG3.sBox_of_commute sStep sRoot SBox.toG3 rfl toG3_sStep p

theorem inS_toG3 (B : SBox) (a b E : ℝ) : CKLaneG3.InS B.toG3 a b E ↔ InS B a b E := Iff.rfl

theorem ParentS.toG3 {B : SBox} (h : ParentS B) : CKLaneG3.ParentS B.toG3 :=
  fun k μ hin => h k μ hin

/-- Parent dominance on the lane-local box of an archived path gives the canonical `SLeafOK`. -/
theorem sLeafOK_of_parentS_sBox {p : List ℕ} (h : ParentS (sBox p)) :
    CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  rw [← toG3_sBox]
  exact CKLaneG3.sLeafOK_of_parentS h.toG3

/-- The checker's conclusion on `pathBox p` gives the canonical `SLeafOK (sBox p)`. -/
theorem ParentDominance.sLeafOK {p : List ℕ} (h : ParentDominance (pathBox p)) :
    CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  sLeafOK_of_parentS_sBox h.toParentS

/-- **Canary (canonical form).** The hardest archived `parent_tail` leaf `4444444444444444513`. -/
theorem Canary.canary_sLeafOK : CKLaneG3.SLeafOK (CKLaneG3.sBox Canary.path) :=
  Canary.canary_dominance.sLeafOK

/-- Parent dominance in the canonical form (for consumers preferring `CKLaneG3.ParentS`). -/
theorem Canary.canary_parentG3 : CKLaneG3.ParentS (CKLaneG3.sBox Canary.path) := by
  rw [← toG3_sBox]
  exact Canary.canary_parentS.toG3

end CKLaneM06

import CKLaneM08.Checker
import CKLaneG3.SCover

/-!
# Lane M08 → canonical (S) cover adapter (`CKLaneG3.SCover`)

`CKLaneM08.Box` / `root` / `step` / `boxOfPath` / `InBox` are field-for-field the canonical
`CKLaneG3.SBox` / `sRoot` / `sStep` / `sBox` / `InS`; `Sem` is `CKLaneG3.SemS`.
-/

set_option autoImplicit false

namespace CKLaneM08

/-- The identity-on-fields map to the canonical (S) box type. -/
def toS (B : Box) : CKLaneG3.SBox := ⟨B.x0, B.x1, B.b0, B.b1, B.t0, B.t1⟩

theorem toS_root : toS root = CKLaneG3.sRoot := rfl

theorem toS_step (B : Box) (d : ℕ) : toS (step B d) = CKLaneG3.sStep (toS B) d := by
  rcases d with _ | _ | _ | _ | _ | _ | d <;> rfl

theorem toS_boxOfPath (p : List ℕ) : toS (boxOfPath p) = CKLaneG3.sBox p :=
  CKLaneG3.sBox_of_commute step root toS toS_root toS_step p

theorem semS_of_sem {B : Box} (h : Sem B) : CKLaneG3.SemS (toS B) :=
  fun k μ hin => h k μ hin

theorem sLeafOK_of_sem {B : Box} (h : Sem B) : CKLaneG3.SLeafOK (toS B) :=
  CKLaneG3.sLeafOK_of_semS (semS_of_sem h)

/-- Canonical-form leaf theorem for an archived path. -/
theorem sLeafOK_of_path {p : List ℕ} (h : Sem (boxOfPath p)) : CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  rw [← toS_boxOfPath p]
  exact sLeafOK_of_sem h

end CKLaneM08

#check @CKLaneM08.toS_boxOfPath
#check @CKLaneM08.sLeafOK_of_path
#print axioms CKLaneM08.toS_boxOfPath
#print axioms CKLaneM08.sLeafOK_of_path

import CKLaneM06.Canary
import CKLaneM06.SForm

/-!
# Lane M06 canary in the BRIEF §7 same-side form

The hardest archived `parent_tail` leaf `4444444444444444513`, restated over `InS (sBox path)`
(exact `COVER.reconstruct` box, BRIEF §7 membership).
-/

set_option autoImplicit false

namespace CKLaneM06.Canary

open CKLaneM06

/-- The exact archived box in BRIEF §7 fields. -/
theorem sBox_eq : sBox path = ⟨16, 32, 17 / 64, 1 / 2, 1 / 131072, 1 / 65536⟩ := by
  decide +kernel

/-- **Canary (BRIEF §7 form).** Parent dominance on `InS (sBox path)`. -/
theorem canary_parentS : ParentS (sBox path) := canary_dominance.toParentS

/-- **Canary (BRIEF §7 form, strict psi-activity owner).** -/
theorem canary_ownerS : OwnerS (sBox path) := canary_parentS.ownerS

end CKLaneM06.Canary

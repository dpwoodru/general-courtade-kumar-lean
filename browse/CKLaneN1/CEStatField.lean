import CKLaneN1.CEStatCapital

set_option autoImplicit false

/-!
# Lane N1: `leftStationary` from the three CE-stat rows still open elsewhere (CONDITIONAL)

Rows 1 (`retainedDomainExclusion`) and 2 (`capitalExclusion`) are closed in lane N1. Rows 3
(`TransverseCurvatureOwner`) and 4 (`A3LeafUnion`) belong to lane M07, row 5 (`HighTCExclusion`) to
lane A1. This adapter is CONDITIONAL on those three rows; it closes nothing by itself.
-/

namespace CKLaneN1.CEStat

open GeneralCK GeneralCK.SmallMeanPhiCutoff

/-- CONDITIONAL (not a closure): the field `leftStationary` (at `S = retainedCutoff`) from CE-stat
rows 3, 4, 5. -/
theorem leftStationary_of_rows345 (h3 : TransverseCurvatureOwner) (h4 : A3LeafUnion)
    (h5 : HighTCExclusion) : LeftStationaryField :=
  leftStationary_of_owners ⟨retainedDomainExclusion, Capital.capitalExclusion, h3, h4, h5⟩

end CKLaneN1.CEStat

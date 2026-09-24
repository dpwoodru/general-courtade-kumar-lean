import CKRoute.Manuscript
import CKLaneD.OCompact

/-!
# Binding Lane D's (O)-tree aggregation to the manuscript row `OP_Compact`

`CKLaneD.OCompact.OPCompactRow` is a verbatim copy of `CKRoute.OP_Compact`; the
equivalence below is definitional. The aggregation hypothesis ranges over all
29,495 leaves of the archived outer-opposite partition `CKLaneD.ArchTree.archTree`
(root `[3,28] × [1,28] × [0,1]` in `(u,v,t)`), each on its full archived image.
-/

namespace CKRoute

open GeneralCK

theorem opCompact_iff_laneD : OP_Compact ↔ CKLaneD.OCompact.OPCompactRow := Iff.rfl

/-- Conditional: the (O) row from per-leaf ownership of every archived leaf. -/
theorem opCompact_of_archLeaves
    (h : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves,
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)) :
    OP_Compact :=
  opCompact_iff_laneD.mpr (CKLaneD.OCompact.opCompact_of_leaves h)

end CKRoute

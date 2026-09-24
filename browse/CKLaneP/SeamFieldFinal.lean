/-
Lane P — FINAL instantiation of the seam field (merged provider root P/genroot).

`GeneralCK.FinalProductionAssemblyPositiveCutoff.ProductionOwners.seam :
   StrictSeamMinimizerExclusion retainedCutoff`   (GeneralCK/PureGapSeamOwner.lean).

Proof: `seam_exclusion_of_box` (CKLaneP.SeamFinal) reduces the field to the root box
`SeamBox 0 (1/20000) 0 2` in `(p, t)` coordinates (`p = entropyInverse e`, `q = entropyInverse f`,
`t = (q − p)/(S/2 − p)`); the box is covered by the kernel-checked split trees of
`CKLaneP.Cells.S3.*` (`seamBox_all`, leaves: certified N-A/N-B/W-A/W-K/W-B/V cells and the
small-scale lemma `seamT_small` for `q ≤ 1/200000`).  The only external input is the compiled
double-cap owner `canonicalDoubleCapEntropyEndpoints_of_joint_batches` (used for `DC ≥ 0`).
-/
import CKLaneP.SeamAssemblyS3
import CKLaneP.SeamTCells
import GeneralCK.PureGapDoubleCapBatchJointOwnerAdapter

set_option autoImplicit false

namespace CKLaneP

open GeneralCK SmallMeanPhiCutoff

/-- The seam field of the positive-cutoff production owners. -/
theorem seam_field_certified : StrictSeamMinimizerExclusion retainedCutoff := by
  have hbox := Cells.S3.seamBox_all canonicalDoubleCapEntropyEndpoints_of_joint_batches
    (seamT_small canonicalDoubleCapEntropyEndpoints_of_joint_batches)
  have h := seam_exclusion_of_box hbox
  unfold retainedCutoff
  exact h

end CKLaneP

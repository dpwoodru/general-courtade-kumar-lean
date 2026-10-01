/-
Lane P — FINAL instantiation of the `rightLower` field (merged provider root P/genroot).

`rightLower_of_doubleCap` (CKLaneP.RightLower) + the compiled external double-cap owner
`GeneralCK.canonicalDoubleCapEntropyEndpoints_of_joint_batches` (I-A root closure, hardlinked into
P/genroot; the 170 modules shared with ~/gck_lanes/F-C/work/root are byte-identical).
-/
import CKLaneP.RightLower
import GeneralCK.PureGapDoubleCapBatchJointOwnerAdapter

set_option autoImplicit false

namespace CKLaneP

open GeneralCK SmallMeanPhiCutoff

/-- The `rightLower` field of `CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff`. -/
theorem rightLower_certified :
    ∀ e f : ℝ, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff e (entropyInverse f) ≤ entropyInverse f →
      0 ≤ canonicalPureGap (capFiberLower retainedCutoff e (entropyInverse f))
        (entropyInverse f) e f :=
  rightLower_of_doubleCap canonicalDoubleCapEntropyEndpoints_of_joint_batches

/-- The statement above is exactly the type of the structure field. -/
example : (∀ o : CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff,
    ∀ e f : ℝ, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff e (entropyInverse f) ≤ entropyInverse f →
      0 ≤ canonicalPureGap (capFiberLower retainedCutoff e (entropyInverse f))
        (entropyInverse f) e f) := fun o => o.rightLower

end CKLaneP

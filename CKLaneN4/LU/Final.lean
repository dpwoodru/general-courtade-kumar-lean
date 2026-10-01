/-
Lane N4b — FINAL: the `leftUpper` field of
`GeneralCK.CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff` (merged provider P/genroot).

* `f < 1`: `CKLaneN4.LU.leftUpper_lt_one` (certified cover, F-C root modules; byte-identical in genroot);
* `f = 1`: the double-cap value `canonicalPureGap (entropyInverse e) (entropyInverse 1) e 1`, owned by
  `GeneralCK.canonicalDoubleCapEntropyEndpoints_of_joint_batches` (I-A closure in P/genroot) through
  `canonicalPureGap_inverse_doubleCap_nonneg_of_scalar_endpoints`, exactly as Lane P's RightLowerFinal.
-/
import CKLaneN4.LU.Owner
import GeneralCK.PureGapDoubleCapBatchJointOwnerAdapter
import GeneralCK.PureGapCapAnalytic
import GeneralCK.SmallMeanPhiRetainedCutoff

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK SmallMeanPhiCutoff

theorem entropyInverse_one_eq : entropyInverse 1 = 1 / 2 := by
  have h := entropyInverse_H_lower (v := 1 / 2) (by norm_num) le_rfl
  rwa [H_half] at h

/-- The `leftUpper` field of `CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff`. -/
theorem leftUpper_certified :
    ∀ e f : ℝ, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f := by
  intro e f he hef hf _
  rcases lt_or_eq_of_le hf with hf1 | hf1
  · exact leftUpper_lt_one e f he hef hf1
  · subst hf1
    have h := canonicalPureGap_inverse_doubleCap_nonneg_of_scalar_endpoints
      canonicalDoubleCapEntropyEndpoints_of_joint_batches he hef le_rfl
    rwa [entropyInverse_one_eq] at h

/-- The statement above is exactly the type of the structure field. -/
example : (∀ o : CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff,
    ∀ e f : ℝ, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f) := fun o => o.leftUpper

end CKLaneN4.LU

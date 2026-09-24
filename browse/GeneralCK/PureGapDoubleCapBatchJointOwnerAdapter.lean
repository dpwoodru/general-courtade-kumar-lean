import GeneralCK.PureGapDoubleCapLowFirstFifthAssembly
import GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation
import GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.All
import GeneralCK.PureGapDoubleCapLowTailNearZeroOwnerAdapter

/-!
The three sealed cell batches join at the exact closed endpoints
`1/5`, `1/4`, and `2/5`. This module is source-only until all 228 low-middle,
480 compact-middle, and 256 high-middle cell receipts and their aggregations
pass direct named Lean audits. In particular, a generated source or a numerical
preflight does not discharge any premise here.
-/

namespace GeneralCK

theorem doubleCapRemainingRegionsV26_of_joint_batches :
    DoubleCapRemainingRegionsV26 := by
  constructor
  · intro m hm100 hmQuarter
    by_cases hmFifth : m ≤ 1 / 5
    · exact doubleCapLowResidual_nonneg_first_fifth
        (by linarith) hmFifth
    · exact Certificates.DoubleCapMiddle.doubleCapMiddleAggregation.1
        m (by linarith) hmQuarter
  · intro m hmQuarter hmSeven
    by_cases hmTwoFifths : m ≤ 2 / 5
    · exact Certificates.DoubleCapMiddle.doubleCapMiddleAggregation.2
        m hmQuarter.le hmTwoFifths
    · exact Certificates.DoubleCapHighMiddleDerivative.bridgeValueResidual_nonneg
        (by linarith) hmSeven.le

theorem canonicalDoubleCapEntropyEndpoints_of_joint_batches :
    CanonicalDoubleCapEntropyEndpoints :=
  DoubleCapRemainingRegionsV26.toEndpoints
    doubleCapRemainingRegionsV26_of_joint_batches

#print axioms doubleCapRemainingRegionsV26_of_joint_batches
#print axioms canonicalDoubleCapEntropyEndpoints_of_joint_batches

end GeneralCK

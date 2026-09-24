import GeneralCK.PureGapDoubleCapLowTailActualSign
import GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.All

/-! The checked near-zero tail and the sealed low-middle cell aggregation
join on the closed endpoint `1/100`. This source becomes an accepted owner
only after all 228 cells and the split aggregation pass named Lean audits. -/

namespace GeneralCK

theorem doubleCapLowResidual_nonneg_first_fifth {m : ℝ}
    (hm : 0 < m) (hm5 : m ≤ 1 / 5) :
    0 ≤ doubleCapLowResidual m := by
  by_cases hm100 : m ≤ 1 / 100
  · exact doubleCapLowResidual_nonneg_near_zero hm hm100
  · exact Certificates.DoubleCapLowMiddleAggregation.doubleCapLowMiddleAggregation
      m (by linarith [lt_of_not_ge hm100]) hm5

#print axioms doubleCapLowResidual_nonneg_first_fifth

end GeneralCK

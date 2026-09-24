import GeneralCK.PureGapDoubleCapLowTailActualSign
import GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsHybridOwnerAdapter

/-! The actual near-zero low-slope theorem removes the low-tail sign
premise from the current double-cap owner. -/

namespace GeneralCK

def DoubleCapRemainingRegionsV26 : Prop :=
  (∀ m : ℝ, 1 / 100 < m → m ≤ 1 / 4 → 0 ≤ doubleCapLowResidual m) ∧
  (∀ m : ℝ, 1 / 4 < m → m < 7 / 16 → 0 ≤ doubleCapHighResidual m)

theorem DoubleCapRemainingRegionsV26.toEndpoints
    (h : DoubleCapRemainingRegionsV26) :
    CanonicalDoubleCapEntropyEndpoints := by
  apply canonicalDoubleCapEntropyEndpoints_of_remaining_regions_seven
    (a := 1 / 100) (by norm_num) (by norm_num)
  · intro m hm hm100
    exact doubleCapLowSlopeResidual_nonneg_near_zero hm hm100
  · exact h.1
  · exact h.2

#print axioms DoubleCapRemainingRegionsV26.toEndpoints

end GeneralCK

import GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsValue
import GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsHybridOwnerAdapter

/-! Exact hybrid owner with `b=7/16`, plus a named bridge to the frozen
V16 `b=15/32` adapter. The remaining owner regions are hypotheses. -/

namespace GeneralCK

theorem doubleCapHybridSlopeCertificate_of_remaining_regions_seven
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 7 / 16 →
      0 ≤ doubleCapHighResidual m) :
    DoubleCapHybridSlopeCertificate a (7 / 16) := by
  refine ⟨haPos, haQuarter, ?_, ?_, hlowSlope, hlowMiddle,
    hhighMiddle, ?_⟩
  · norm_num
  · norm_num
  · intro m hm7 hmh
    exact doubleCapHighSlopeResidual_nonneg_on_seven_tail hm7 hmh

theorem highMiddle_fifteenth_of_highMiddle_seven
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 7 / 16 →
      0 ≤ doubleCapHighResidual m) :
    ∀ m : ℝ, 1 / 4 < m → m < 15 / 32 →
      0 ≤ doubleCapHighResidual m := by
  intro m hmq hm15
  by_cases hm7 : 7 / 16 ≤ m
  · exact doubleCapHighResidual_nonneg_on_seven_tail hm7
      (by linarith : m < 1 / 2)
  · exact hhighMiddle m hmq (lt_of_not_ge hm7)

theorem canonicalDoubleCapEntropyEndpoints_of_remaining_regions_seven
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 7 / 16 →
      0 ≤ doubleCapHighResidual m) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_hybridSlopeCertificate
    (doubleCapHybridSlopeCertificate_of_remaining_regions_seven
      haPos haQuarter hlowSlope hlowMiddle hhighMiddle)

theorem canonicalDoubleCapEntropyEndpoints_via_frozen_v16
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 7 / 16 →
      0 ≤ doubleCapHighResidual m) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_remaining_regions_fifteenth
    haPos haQuarter hlowSlope hlowMiddle
    (highMiddle_fifteenth_of_highMiddle_seven hhighMiddle)

#print axioms doubleCapHybridSlopeCertificate_of_remaining_regions_seven
#print axioms highMiddle_fifteenth_of_highMiddle_seven
#print axioms canonicalDoubleCapEntropyEndpoints_of_remaining_regions_seven
#print axioms canonicalDoubleCapEntropyEndpoints_via_frozen_v16

end GeneralCK

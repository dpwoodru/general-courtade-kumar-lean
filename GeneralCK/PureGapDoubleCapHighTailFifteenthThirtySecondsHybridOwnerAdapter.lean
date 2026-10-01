import GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsValue
import GeneralCK.PureGapDoubleCapHighTailHybridOwnerAdapter

/-! Exact hybrid owner with `b=15/32`, plus a bridge to the frozen V15
`b=31/64` adapter. Remaining low and high-middle regions are hypotheses. -/

namespace GeneralCK

theorem doubleCapHybridSlopeCertificate_of_remaining_regions_fifteenth
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 15 / 32 →
      0 ≤ doubleCapHighResidual m) :
    DoubleCapHybridSlopeCertificate a (15 / 32) := by
  refine ⟨haPos, haQuarter, ?_, ?_, hlowSlope, hlowMiddle,
    hhighMiddle, ?_⟩
  · norm_num
  · norm_num
  · intro m hm15 hmh
    exact doubleCapHighSlopeResidual_nonneg_on_fifteenth_tail hm15 hmh

theorem highMiddle_thirtyone_of_highMiddle_fifteenth
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 15 / 32 →
      0 ≤ doubleCapHighResidual m) :
    ∀ m : ℝ, 1 / 4 < m → m < 31 / 64 →
      0 ≤ doubleCapHighResidual m := by
  intro m hmq hm31
  by_cases hm15 : 15 / 32 ≤ m
  · exact doubleCapHighResidual_nonneg_on_fifteenth_tail hm15
      (by linarith : m < 1 / 2)
  · exact hhighMiddle m hmq (lt_of_not_ge hm15)

theorem canonicalDoubleCapEntropyEndpoints_of_remaining_regions_fifteenth
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 15 / 32 →
      0 ≤ doubleCapHighResidual m) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_hybridSlopeCertificate
    (doubleCapHybridSlopeCertificate_of_remaining_regions_fifteenth
      haPos haQuarter hlowSlope hlowMiddle hhighMiddle)

theorem canonicalDoubleCapEntropyEndpoints_via_frozen_v15
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 15 / 32 →
      0 ≤ doubleCapHighResidual m) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_remaining_regions
    haPos haQuarter hlowSlope hlowMiddle
    (highMiddle_thirtyone_of_highMiddle_fifteenth hhighMiddle)

#print axioms doubleCapHybridSlopeCertificate_of_remaining_regions_fifteenth
#print axioms highMiddle_thirtyone_of_highMiddle_fifteenth
#print axioms canonicalDoubleCapEntropyEndpoints_of_remaining_regions_fifteenth
#print axioms canonicalDoubleCapEntropyEndpoints_via_frozen_v15

end GeneralCK

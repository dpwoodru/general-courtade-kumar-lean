import GeneralCK.PureGapDoubleCapHighTailActualSign

/-! Exact hybrid cap owner interface with the accepted high slope tail
beginning at `31/64`. Only the three remaining owner regions are hypotheses. -/

namespace GeneralCK

theorem doubleCapHybridSlopeCertificate_of_remaining_regions
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 31 / 64 →
      0 ≤ doubleCapHighResidual m) :
    DoubleCapHybridSlopeCertificate a (31 / 64) := by
  refine ⟨haPos, haQuarter, ?_, ?_, hlowSlope, hlowMiddle,
    hhighMiddle, ?_⟩
  · norm_num
  · norm_num
  · intro m hm31 hmh
    exact doubleCapHighSlopeResidual_nonneg_on_explicit_high_tail hm31 hmh

theorem canonicalDoubleCapEntropyEndpoints_of_remaining_regions
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 31 / 64 →
      0 ≤ doubleCapHighResidual m) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_hybridSlopeCertificate
    (doubleCapHybridSlopeCertificate_of_remaining_regions
      haPos haQuarter hlowSlope hlowMiddle hhighMiddle)

#print axioms doubleCapHybridSlopeCertificate_of_remaining_regions
#print axioms canonicalDoubleCapEntropyEndpoints_of_remaining_regions

end GeneralCK

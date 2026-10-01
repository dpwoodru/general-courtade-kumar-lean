import E8MiddleCertificate
import E8PadeTail

namespace GeneralCK.E8RatioMonotonicity

open Set Certificates.E8HistoricalLogConvexityBridge

/-- The initial analytic interval, 28 checked middle cells, and the Padé tail
cover the entire positive stable parameter axis. -/
theorem stableL_nonnegative {a : ℝ} (ha : 0 < a) : 0 ≤ stableL a := by
  by_cases hsmall : a ≤ 1 / 4
  · linarith [stableL_ge_three_initial ha hsmall]
  · by_cases hmiddle : a ≤ 3 / 2
    · exact (MiddleCertificate.stableL_pos_middle (le_of_not_ge hsmall) hmiddle).le
    · exact stableL_nonneg_of_three_halves (le_of_not_ge hmiddle)

theorem e8RatioMonotone : MonotoneOn ratio (Ioi 0) :=
  ratio_monotone_iff_stableL_nonneg.mpr (fun _ ha => stableL_nonnegative ha)

theorem e8ReciprocalConvex : ConvexOn ℝ (Ioi 0) reciprocal :=
  reciprocal_convex_iff_ratio_monotone.mpr e8RatioMonotone

theorem e8Theta_ratio_monotone :
    MonotoneOn (fun u : ℝ => -deriv (deriv e8Theta) u / (deriv e8Theta u) ^ 2)
      (Ioi 0) := e8RatioMonotone

theorem e8Theta_reciprocal_convex :
    ConvexOn ℝ (Ioi 0) (fun u : ℝ => 1 / deriv e8Theta u) := by
  have hf : (fun u : ℝ => 1 / deriv e8Theta u) = reciprocal := by
    funext u
    simp only [one_div, reciprocal]
  rw [hf]
  exact e8ReciprocalConvex

theorem e8StableJetNumeratorNonnegative : E8StableLogDerivativeJetNumeratorNonnegative :=
  stable_numerator_nonnegative_iff_ratio_monotone.mpr e8RatioMonotone

theorem e8LargeSStructureCertified : E8LargeSStructure :=
  largeSStructure_of_ratio_monotone e8RatioMonotone

theorem e8LargeSCertified : E8PositiveOn (fun s _ => (63 / 20 : ℝ) ≤ s) :=
  largeS_of_ratio_monotone e8RatioMonotone

#print axioms stableL_nonnegative
#print axioms e8RatioMonotone
#print axioms e8ReciprocalConvex
#print axioms e8Theta_ratio_monotone
#print axioms e8Theta_reciprocal_convex
#print axioms e8StableJetNumeratorNonnegative
#print axioms e8LargeSStructureCertified
#print axioms e8LargeSCertified

end GeneralCK.E8RatioMonotonicity

import GeneralCK.Certificates.Generated.MidpointFamily.FullCertificate
import GeneralCK.Certificates.Generated.MidpointNextFamily.FullCertificate
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.FullCertificate
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.FullCertificate
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.FullCertificate
import GeneralCK.Certificates.Generated.LowRatioFamily.FullCertificate

namespace GeneralCK.Certificates.ReflectionMidpointCombinedCoverage

open GeneralCK.Reflection GeneralCK.Certificates.Reflection

/-- The five completed midpoint families give one contiguous certified strip. -/
theorem full_midpoint_through_post_next_band {a z : ℝ}
    (ha : Bounds (3 / 20) (999 / 1000) a)
    (hz : Bounds (1 / 1000) (43 / 500) z) :
    0 < curvature a (a * z) := by
  by_cases h0 : z ≤ (1 / 100 : ℝ)
  · exact ReflectionMidpointFamily.full_midpoint_strip ha ⟨hz.1, h0⟩
  by_cases h1 : z ≤ (1 / 20 : ℝ)
  · exact ReflectionMidpointNextFamily.full_midpoint_next_strip ha
      ⟨le_of_lt (lt_of_not_ge h0), h1⟩
  by_cases h2 : z ≤ (406621 / 5000000 : ℝ)
  · exact ReflectionMidpointExtensionFamily.full_midpoint_extension ha
      ⟨le_of_lt (lt_of_not_ge h1), h2⟩
  by_cases h3 : z ≤ (17 / 200 : ℝ)
  · exact ReflectionMidpointNextBandFamily.full_midpoint_next_band ha
      ⟨le_of_lt (lt_of_not_ge h2), h3⟩
  · exact ReflectionMidpointPostNextBandFamily.full_midpoint_post_next_band ha
      ⟨le_of_lt (lt_of_not_ge h3), hz.2⟩

/-- The low-ratio family and the five midpoint families form one positive-ratio strip. -/
theorem full_positive_ratio_through_post_next_band {a z : ℝ}
    (ha : Bounds (3 / 20) (999 / 1000) a)
    (hz : z ∈ Set.Ioc (0 : ℝ) (43 / 500)) :
    0 < curvature a (a * z) := by
  by_cases h0 : z ≤ (1 / 1000 : ℝ)
  · exact LowRatioFamily.full_low_ratio_strip ha ⟨hz.1, h0⟩
  · exact full_midpoint_through_post_next_band ha
      ⟨le_of_lt (lt_of_not_ge h0), hz.2⟩

#print axioms full_midpoint_through_post_next_band
#print axioms full_positive_ratio_through_post_next_band

end GeneralCK.Certificates.ReflectionMidpointCombinedCoverage

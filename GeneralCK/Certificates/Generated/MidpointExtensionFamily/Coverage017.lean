import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0272
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0273
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0274
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0275
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0276
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0277
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage017 {a z : ℝ} (ha : Bounds (163/200) (999/1000) a)
    (hz : Bounds (1/20) (81/1000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (37/40:ℝ)
  · by_cases h1 : a ≤ (17/20:ℝ)
    · exact Cell0272.curvature_pos ⟨ha.1,h1⟩ hz
    · by_cases h2 : a ≤ (177/200:ℝ)
      · exact Cell0273.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h2⟩ hz
      · exact Cell0274.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h0⟩ hz
  · by_cases h3 : a ≤ (241/250:ℝ)
    · exact Cell0275.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h3⟩ hz
    · by_cases h4 : a ≤ (497/500:ℝ)
      · exact Cell0276.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h4⟩ hz
      · exact Cell0277.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

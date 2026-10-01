import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0831
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0832
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0833
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0834
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0835
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0836
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0837
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0838
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0839
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage053 {a z : ℝ} (ha : Bounds (361/500) (999/1000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (17/20:ℝ)
  · by_cases h1 : a ≤ (98/125:ℝ)
    · by_cases h2 : a ≤ (94/125:ℝ)
      · exact Cell0831.curvature_pos ⟨ha.1,h2⟩ hz
      · exact Cell0832.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h1⟩ hz
    · by_cases h3 : a ≤ (163/200:ℝ)
      · exact Cell0833.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h3⟩ hz
      · exact Cell0834.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h0⟩ hz
  · by_cases h4 : a ≤ (93/100:ℝ)
    · by_cases h5 : a ≤ (89/100:ℝ)
      · exact Cell0835.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h5⟩ hz
      · exact Cell0836.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h4⟩ hz
    · by_cases h6 : a ≤ (97/100:ℝ)
      · exact Cell0837.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h6⟩ hz
      · by_cases h7 : a ≤ (249/250:ℝ)
        · exact Cell0838.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h7⟩ hz
        · exact Cell0839.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

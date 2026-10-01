import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0240
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0241
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0242
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0243
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0244
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0245
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0246
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0247
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0248
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0249
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0250
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0251
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0252
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0253
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0254
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0255
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage015 {a z : ℝ} (ha : Bounds (44/125) (239/500) a)
    (hz : Bounds (1/20) (81/1000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (401/1000:ℝ)
  · by_cases h1 : a ≤ (187/500:ℝ)
    · by_cases h2 : a ≤ (181/500:ℝ)
      · by_cases h3 : a ≤ (357/1000:ℝ)
        · exact Cell0240.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0241.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (46/125:ℝ)
        · exact Cell0242.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0243.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (387/1000:ℝ)
      · by_cases h6 : a ≤ (19/50:ℝ)
        · exact Cell0244.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0245.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (197/500:ℝ)
        · exact Cell0246.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0247.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (87/200:ℝ)
    · by_cases h9 : a ≤ (417/1000:ℝ)
      · by_cases h10 : a ≤ (409/1000:ℝ)
        · exact Cell0248.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0249.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (213/500:ℝ)
        · exact Cell0250.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0251.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (91/200:ℝ)
      · by_cases h13 : a ≤ (89/200:ℝ)
        · exact Cell0252.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0253.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (233/500:ℝ)
        · exact Cell0254.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0255.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

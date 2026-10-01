import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0256
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0257
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0258
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0259
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0260
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0261
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0262
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0263
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0264
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0265
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0266
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0267
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0268
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0269
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0270
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0271
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage016 {a z : ℝ} (ha : Bounds (239/500) (163/200) a)
    (hz : Bounds (1/20) (81/1000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (299/500:ℝ)
  · by_cases h1 : a ≤ (53/100:ℝ)
    · by_cases h2 : a ≤ (251/500:ℝ)
      · by_cases h3 : a ≤ (49/100:ℝ)
        · exact Cell0256.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0257.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (129/250:ℝ)
        · exact Cell0258.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0259.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (281/500:ℝ)
      · by_cases h6 : a ≤ (273/500:ℝ)
        · exact Cell0260.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0261.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (29/50:ℝ)
        · exact Cell0262.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0263.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (69/100:ℝ)
    · by_cases h9 : a ≤ (16/25:ℝ)
      · by_cases h10 : a ≤ (309/500:ℝ)
        · exact Cell0264.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0265.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (83/125:ℝ)
        · exact Cell0266.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0267.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (187/250:ℝ)
      · by_cases h13 : a ≤ (359/500:ℝ)
        · exact Cell0268.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0269.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (39/50:ℝ)
        · exact Cell0270.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0271.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

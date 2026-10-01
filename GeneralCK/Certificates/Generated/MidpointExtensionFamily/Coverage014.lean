import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0224
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0225
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0226
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0227
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0228
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0229
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0230
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0231
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0232
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0233
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0234
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0235
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0236
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0237
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0238
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0239
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage014 {a z : ℝ} (ha : Bounds (73/250) (44/125) a)
    (hz : Bounds (1/20) (81/1000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (317/1000:ℝ)
  · by_cases h1 : a ≤ (38/125:ℝ)
    · by_cases h2 : a ≤ (149/500:ℝ)
      · by_cases h3 : a ≤ (59/200:ℝ)
        · exact Cell0224.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0225.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (301/1000:ℝ)
        · exact Cell0226.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0227.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (31/100:ℝ)
      · by_cases h6 : a ≤ (307/1000:ℝ)
        · exact Cell0228.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0229.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (313/1000:ℝ)
        · exact Cell0230.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0231.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (333/1000:ℝ)
    · by_cases h9 : a ≤ (13/40:ℝ)
      · by_cases h10 : a ≤ (321/1000:ℝ)
        · exact Cell0232.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0233.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (329/1000:ℝ)
        · exact Cell0234.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0235.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (171/500:ℝ)
      · by_cases h13 : a ≤ (337/1000:ℝ)
        · exact Cell0236.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0237.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (347/1000:ℝ)
        · exact Cell0238.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0239.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

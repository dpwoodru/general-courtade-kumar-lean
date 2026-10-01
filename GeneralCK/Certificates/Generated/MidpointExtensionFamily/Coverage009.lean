import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0144
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0145
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0146
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0147
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0148
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0149
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0150
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0151
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0152
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0153
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0154
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0155
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0156
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0157
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0158
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0159
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage009 {a z : ℝ} (ha : Bounds (479/2500) (101/500) a)
    (hz : Bounds (1/20) (81/1000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (983/5000:ℝ)
  · by_cases h1 : a ≤ (97/500:ℝ)
    · by_cases h2 : a ≤ (241/1250:ℝ)
      · by_cases h3 : a ≤ (961/5000:ℝ)
        · exact Cell0144.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0145.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (967/5000:ℝ)
        · exact Cell0146.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0147.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (122/625:ℝ)
      · by_cases h6 : a ≤ (973/5000:ℝ)
        · exact Cell0148.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0149.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (979/5000:ℝ)
        · exact Cell0150.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0151.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (999/5000:ℝ)
    · by_cases h9 : a ≤ (991/5000:ℝ)
      · by_cases h10 : a ≤ (987/5000:ℝ)
        · exact Cell0152.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0153.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (199/1000:ℝ)
        · exact Cell0154.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0155.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (201/1000:ℝ)
      · by_cases h13 : a ≤ (401/2000:ℝ)
        · exact Cell0156.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0157.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (403/2000:ℝ)
        · exact Cell0158.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0159.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

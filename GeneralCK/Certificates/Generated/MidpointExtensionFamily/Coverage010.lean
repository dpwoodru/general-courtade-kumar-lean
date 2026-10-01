import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0160
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0161
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0162
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0163
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0164
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0165
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0166
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0167
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0168
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0169
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0170
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0171
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0172
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0173
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0174
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0175
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage010 {a z : ℝ} (ha : Bounds (101/500) (427/2000) a)
    (hz : Bounds (1/20) (81/1000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (103/500:ℝ)
  · by_cases h1 : a ≤ (51/250:ℝ)
    · by_cases h2 : a ≤ (203/1000:ℝ)
      · by_cases h3 : a ≤ (81/400:ℝ)
        · exact Cell0160.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0161.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (407/2000:ℝ)
        · exact Cell0162.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0163.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (41/200:ℝ)
      · by_cases h6 : a ≤ (409/2000:ℝ)
        · exact Cell0164.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0165.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (411/2000:ℝ)
        · exact Cell0166.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0167.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (419/2000:ℝ)
    · by_cases h9 : a ≤ (83/400:ℝ)
      · by_cases h10 : a ≤ (413/2000:ℝ)
        · exact Cell0168.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0169.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (417/2000:ℝ)
        · exact Cell0170.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0171.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (423/2000:ℝ)
      · by_cases h13 : a ≤ (421/2000:ℝ)
        · exact Cell0172.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0173.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (17/80:ℝ)
        · exact Cell0174.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0175.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

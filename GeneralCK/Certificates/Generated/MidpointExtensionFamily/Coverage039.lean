import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0607
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0608
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0609
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0610
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0611
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0612
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0613
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0614
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0615
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0616
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0617
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0618
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0619
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0620
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0621
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0622
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage039 {a z : ℝ} (ha : Bounds (159/1000) (811/5000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (803/5000:ℝ)
  · by_cases h1 : a ≤ (799/5000:ℝ)
    · by_cases h2 : a ≤ (797/5000:ℝ)
      · by_cases h3 : a ≤ (199/1250:ℝ)
        · exact Cell0607.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0608.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (399/2500:ℝ)
        · exact Cell0609.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0610.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (801/5000:ℝ)
      · by_cases h6 : a ≤ (4/25:ℝ)
        · exact Cell0611.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0612.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (401/2500:ℝ)
        · exact Cell0613.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0614.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (807/5000:ℝ)
    · by_cases h9 : a ≤ (161/1000:ℝ)
      · by_cases h10 : a ≤ (201/1250:ℝ)
        · exact Cell0615.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0616.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (403/2500:ℝ)
        · exact Cell0617.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0618.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (809/5000:ℝ)
      · by_cases h13 : a ≤ (101/625:ℝ)
        · exact Cell0619.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0620.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (81/500:ℝ)
        · exact Cell0621.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0622.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0502
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0503
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0504
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0505
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0506
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0507
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0508
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0509
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0510
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0511
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0512
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0513
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0514
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0515
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0516
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0517
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage032 {a z : ℝ} (ha : Bounds (283/1000) (337/1000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (307/1000:ℝ)
  · by_cases h1 : a ≤ (59/200:ℝ)
    · by_cases h2 : a ≤ (289/1000:ℝ)
      · by_cases h3 : a ≤ (143/500:ℝ)
        · exact Cell0502.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0503.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (73/250:ℝ)
        · exact Cell0504.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0505.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (301/1000:ℝ)
      · by_cases h6 : a ≤ (149/500:ℝ)
        · exact Cell0506.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0507.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (38/125:ℝ)
        · exact Cell0508.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0509.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (321/1000:ℝ)
    · by_cases h9 : a ≤ (313/1000:ℝ)
      · by_cases h10 : a ≤ (31/100:ℝ)
        · exact Cell0510.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0511.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (317/1000:ℝ)
        · exact Cell0512.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0513.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (329/1000:ℝ)
      · by_cases h13 : a ≤ (13/40:ℝ)
        · exact Cell0514.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0515.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (333/1000:ℝ)
        · exact Cell0516.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0517.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

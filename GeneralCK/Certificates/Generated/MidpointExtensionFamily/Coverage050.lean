import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0783
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0784
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0785
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0786
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0787
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0788
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0789
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0790
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0791
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0792
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0793
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0794
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0795
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0796
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0797
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0798
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage050 {a z : ℝ} (ha : Bounds (283/1000) (337/1000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (307/1000:ℝ)
  · by_cases h1 : a ≤ (59/200:ℝ)
    · by_cases h2 : a ≤ (289/1000:ℝ)
      · by_cases h3 : a ≤ (143/500:ℝ)
        · exact Cell0783.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0784.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (73/250:ℝ)
        · exact Cell0785.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0786.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (301/1000:ℝ)
      · by_cases h6 : a ≤ (149/500:ℝ)
        · exact Cell0787.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0788.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (38/125:ℝ)
        · exact Cell0789.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0790.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (321/1000:ℝ)
    · by_cases h9 : a ≤ (313/1000:ℝ)
      · by_cases h10 : a ≤ (31/100:ℝ)
        · exact Cell0791.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0792.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (317/1000:ℝ)
        · exact Cell0793.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0794.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (329/1000:ℝ)
      · by_cases h13 : a ≤ (13/40:ℝ)
        · exact Cell0795.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0796.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (333/1000:ℝ)
        · exact Cell0797.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0798.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

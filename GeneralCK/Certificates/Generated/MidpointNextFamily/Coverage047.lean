import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0752
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0753
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0754
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0755
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0756
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0757
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0758
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0759
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0760
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0761
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0762
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0763
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0764
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0765
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0766
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0767
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage047 {a z : ℝ} (ha : Bounds (88/125) (92/125) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(18/25:ℝ)
  · by_cases h1 : a≤(89/125:ℝ)
    · by_cases h2 : a≤(177/250:ℝ)
      · by_cases h3 : a≤(353/500:ℝ)
        · exact Cell0752.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0753.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(71/100:ℝ)
        · exact Cell0754.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0755.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(179/250:ℝ)
      · by_cases h6 : a≤(357/500:ℝ)
        · exact Cell0756.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0757.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(359/500:ℝ)
        · exact Cell0758.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0759.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(91/125:ℝ)
    · by_cases h9 : a≤(181/250:ℝ)
      · by_cases h10 : a≤(361/500:ℝ)
        · exact Cell0760.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0761.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(363/500:ℝ)
        · exact Cell0762.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0763.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(183/250:ℝ)
      · by_cases h13 : a≤(73/100:ℝ)
        · exact Cell0764.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0765.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(367/500:ℝ)
        · exact Cell0766.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0767.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

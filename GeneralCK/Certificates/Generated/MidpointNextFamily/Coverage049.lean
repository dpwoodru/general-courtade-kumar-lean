import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0784
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0785
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0786
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0787
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0788
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0789
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0790
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0791
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0792
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0793
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0794
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0795
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0796
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0797
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0798
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0799
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage049 {a z : ℝ} (ha : Bounds (96/125) (4/5) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(98/125:ℝ)
  · by_cases h1 : a≤(97/125:ℝ)
    · by_cases h2 : a≤(193/250:ℝ)
      · by_cases h3 : a≤(77/100:ℝ)
        · exact Cell0784.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0785.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(387/500:ℝ)
        · exact Cell0786.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0787.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(39/50:ℝ)
      · by_cases h6 : a≤(389/500:ℝ)
        · exact Cell0788.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0789.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(391/500:ℝ)
        · exact Cell0790.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0791.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(99/125:ℝ)
    · by_cases h9 : a≤(197/250:ℝ)
      · by_cases h10 : a≤(393/500:ℝ)
        · exact Cell0792.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0793.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(79/100:ℝ)
        · exact Cell0794.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0795.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(199/250:ℝ)
      · by_cases h13 : a≤(397/500:ℝ)
        · exact Cell0796.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0797.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(399/500:ℝ)
        · exact Cell0798.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0799.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

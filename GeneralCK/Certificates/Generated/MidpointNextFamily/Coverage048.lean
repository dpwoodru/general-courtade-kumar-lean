import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0768
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0769
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0770
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0771
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0772
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0773
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0774
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0775
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0776
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0777
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0778
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0779
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0780
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0781
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0782
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0783
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage048 {a z : ℝ} (ha : Bounds (92/125) (96/125) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(94/125:ℝ)
  · by_cases h1 : a≤(93/125:ℝ)
    · by_cases h2 : a≤(37/50:ℝ)
      · by_cases h3 : a≤(369/500:ℝ)
        · exact Cell0768.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0769.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(371/500:ℝ)
        · exact Cell0770.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0771.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(187/250:ℝ)
      · by_cases h6 : a≤(373/500:ℝ)
        · exact Cell0772.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0773.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(3/4:ℝ)
        · exact Cell0774.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0775.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(19/25:ℝ)
    · by_cases h9 : a≤(189/250:ℝ)
      · by_cases h10 : a≤(377/500:ℝ)
        · exact Cell0776.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0777.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(379/500:ℝ)
        · exact Cell0778.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0779.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(191/250:ℝ)
      · by_cases h13 : a≤(381/500:ℝ)
        · exact Cell0780.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0781.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(383/500:ℝ)
        · exact Cell0782.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0783.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

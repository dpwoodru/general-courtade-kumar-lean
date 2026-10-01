import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0608
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0609
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0610
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0611
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0612
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0613
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0614
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0615
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0616
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0617
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0618
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0619
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0620
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0621
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0622
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0623
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage038 {a z : ℝ} (ha : Bounds (229/500) (237/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(233/500:ℝ)
  · by_cases h1 : a≤(231/500:ℝ)
    · by_cases h2 : a≤(23/50:ℝ)
      · by_cases h3 : a≤(459/1000:ℝ)
        · exact Cell0608.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0609.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(461/1000:ℝ)
        · exact Cell0610.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0611.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(58/125:ℝ)
      · by_cases h6 : a≤(463/1000:ℝ)
        · exact Cell0612.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0613.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(93/200:ℝ)
        · exact Cell0614.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0615.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(47/100:ℝ)
    · by_cases h9 : a≤(117/250:ℝ)
      · by_cases h10 : a≤(467/1000:ℝ)
        · exact Cell0616.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0617.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(469/1000:ℝ)
        · exact Cell0618.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0619.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(59/125:ℝ)
      · by_cases h13 : a≤(471/1000:ℝ)
        · exact Cell0620.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0621.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(473/1000:ℝ)
        · exact Cell0622.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0623.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

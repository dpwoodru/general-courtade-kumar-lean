import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0096
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0097
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0098
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0099
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0100
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0101
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0102
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0103
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0104
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0105
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0106
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0107
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0108
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0109
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0110
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0111
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage006 {a z : ℝ} (ha : Bounds (423/2500) (431/2500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(427/2500:ℝ)
  · by_cases h1 : a≤(17/100:ℝ)
    · by_cases h2 : a≤(106/625:ℝ)
      · by_cases h3 : a≤(847/5000:ℝ)
        · exact Cell0096.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0097.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(849/5000:ℝ)
        · exact Cell0098.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0099.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(213/1250:ℝ)
      · by_cases h6 : a≤(851/5000:ℝ)
        · exact Cell0100.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0101.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(853/5000:ℝ)
        · exact Cell0102.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0103.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(429/2500:ℝ)
    · by_cases h9 : a≤(107/625:ℝ)
      · by_cases h10 : a≤(171/1000:ℝ)
        · exact Cell0104.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0105.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(857/5000:ℝ)
        · exact Cell0106.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0107.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(43/250:ℝ)
      · by_cases h13 : a≤(859/5000:ℝ)
        · exact Cell0108.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0109.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(861/5000:ℝ)
        · exact Cell0110.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0111.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0064
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0065
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0066
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0067
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0068
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0069
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0070
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0071
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0072
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0073
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0074
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0075
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0076
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0077
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0078
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0079
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage004 {a z : ℝ} (ha : Bounds (391/2500) (79/500) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (393/2500:ℝ)
  · by_cases h1 : a ≤ (98/625:ℝ)
    · by_cases h2 : a ≤ (783/5000:ℝ)
      · by_cases h3 : a ≤ (313/2000:ℝ)
        · exact Cell0064.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0065.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (1567/10000:ℝ)
        · exact Cell0066.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0067.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (157/1000:ℝ)
      · by_cases h6 : a ≤ (1569/10000:ℝ)
        · exact Cell0068.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0069.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (1571/10000:ℝ)
        · exact Cell0070.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0071.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (197/1250:ℝ)
    · by_cases h9 : a ≤ (787/5000:ℝ)
      · by_cases h10 : a ≤ (1573/10000:ℝ)
        · exact Cell0072.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0073.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (63/400:ℝ)
        · exact Cell0074.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0075.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (789/5000:ℝ)
      · by_cases h13 : a ≤ (1577/10000:ℝ)
        · exact Cell0076.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0077.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (1579/10000:ℝ)
        · exact Cell0078.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0079.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

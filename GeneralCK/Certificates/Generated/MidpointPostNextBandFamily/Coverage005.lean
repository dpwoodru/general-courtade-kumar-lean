import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0080
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0081
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0082
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0083
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0084
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0085
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0086
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0087
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0088
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0089
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0090
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0091
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0092
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0093
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0094
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0095
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage005 {a z : ℝ} (ha : Bounds (1563/10000) (1579/10000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (1571/10000:ℝ)
  · by_cases h1 : a ≤ (1567/10000:ℝ)
    · by_cases h2 : a ≤ (313/2000:ℝ)
      · by_cases h3 : a ≤ (391/2500:ℝ)
        · exact Cell0080.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0081.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (783/5000:ℝ)
        · exact Cell0082.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0083.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (1569/10000:ℝ)
      · by_cases h6 : a ≤ (98/625:ℝ)
        · exact Cell0084.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0085.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (157/1000:ℝ)
        · exact Cell0086.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0087.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (63/400:ℝ)
    · by_cases h9 : a ≤ (1573/10000:ℝ)
      · by_cases h10 : a ≤ (393/2500:ℝ)
        · exact Cell0088.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0089.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (787/5000:ℝ)
        · exact Cell0090.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0091.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (1577/10000:ℝ)
      · by_cases h13 : a ≤ (197/1250:ℝ)
        · exact Cell0092.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0093.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (789/5000:ℝ)
        · exact Cell0094.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0095.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

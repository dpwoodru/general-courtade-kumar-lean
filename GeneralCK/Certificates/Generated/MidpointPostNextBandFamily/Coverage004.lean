import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0064
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0065
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0066
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0067
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0068
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0069
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0070
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0071
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0072
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0073
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0074
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0075
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0076
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0077
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0078
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0079
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage004 {a z : ℝ} (ha : Bounds (1547/10000) (1563/10000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (311/2000:ℝ)
  · by_cases h1 : a ≤ (1551/10000:ℝ)
    · by_cases h2 : a ≤ (1549/10000:ℝ)
      · by_cases h3 : a ≤ (387/2500:ℝ)
        · exact Cell0064.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0065.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (31/200:ℝ)
        · exact Cell0066.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0067.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (1553/10000:ℝ)
      · by_cases h6 : a ≤ (97/625:ℝ)
        · exact Cell0068.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0069.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (777/5000:ℝ)
        · exact Cell0070.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0071.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (1559/10000:ℝ)
    · by_cases h9 : a ≤ (1557/10000:ℝ)
      · by_cases h10 : a ≤ (389/2500:ℝ)
        · exact Cell0072.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0073.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (779/5000:ℝ)
        · exact Cell0074.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0075.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (1561/10000:ℝ)
      · by_cases h13 : a ≤ (39/250:ℝ)
        · exact Cell0076.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0077.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (781/5000:ℝ)
        · exact Cell0078.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0079.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

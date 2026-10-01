import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0112
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0113
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0114
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0115
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0116
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0117
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0118
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0119
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0120
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0121
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0122
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0123
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0124
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0125
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0126
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0127
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage007 {a z : ℝ} (ha : Bounds (319/2000) (1611/10000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (1603/10000:ℝ)
  · by_cases h1 : a ≤ (1599/10000:ℝ)
    · by_cases h2 : a ≤ (1597/10000:ℝ)
      · by_cases h3 : a ≤ (399/2500:ℝ)
        · exact Cell0112.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0113.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (799/5000:ℝ)
        · exact Cell0114.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0115.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (1601/10000:ℝ)
      · by_cases h6 : a ≤ (4/25:ℝ)
        · exact Cell0116.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0117.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (801/5000:ℝ)
        · exact Cell0118.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0119.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (1607/10000:ℝ)
    · by_cases h9 : a ≤ (321/2000:ℝ)
      · by_cases h10 : a ≤ (401/2500:ℝ)
        · exact Cell0120.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0121.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (803/5000:ℝ)
        · exact Cell0122.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0123.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (1609/10000:ℝ)
      · by_cases h13 : a ≤ (201/1250:ℝ)
        · exact Cell0124.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0125.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (161/1000:ℝ)
        · exact Cell0126.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0127.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

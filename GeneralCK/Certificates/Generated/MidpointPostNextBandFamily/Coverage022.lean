import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0352
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0353
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0354
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0355
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0356
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0357
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0358
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0359
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0360
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0361
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0362
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0363
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0364
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0365
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0366
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0367
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage022 {a z : ℝ} (ha : Bounds (289/1000) (169/500) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (31/100:ℝ)
  · by_cases h1 : a ≤ (597/2000:ℝ)
    · by_cases h2 : a ≤ (117/400:ℝ)
      · by_cases h3 : a ≤ (29/100:ℝ)
        · exact Cell0352.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0353.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (591/2000:ℝ)
        · exact Cell0354.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0355.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (38/125:ℝ)
      · by_cases h6 : a ≤ (301/1000:ℝ)
        · exact Cell0356.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0357.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (307/1000:ℝ)
        · exact Cell0358.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0359.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (161/500:ℝ)
    · by_cases h9 : a ≤ (79/250:ℝ)
      · by_cases h10 : a ≤ (313/1000:ℝ)
        · exact Cell0360.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0361.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (319/1000:ℝ)
        · exact Cell0362.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0363.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (33/100:ℝ)
      · by_cases h13 : a ≤ (163/500:ℝ)
        · exact Cell0364.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0365.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (167/500:ℝ)
        · exact Cell0366.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0367.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

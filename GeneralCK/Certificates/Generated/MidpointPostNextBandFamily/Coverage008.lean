import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0128
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0129
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0130
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0131
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0132
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0133
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0134
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0135
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0136
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0137
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0138
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0139
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0140
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0141
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0142
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0143
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage008 {a z : ℝ} (ha : Bounds (1611/10000) (102/625) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (1619/10000:ℝ)
  · by_cases h1 : a ≤ (323/2000:ℝ)
    · by_cases h2 : a ≤ (1613/10000:ℝ)
      · by_cases h3 : a ≤ (403/2500:ℝ)
        · exact Cell0128.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0129.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (807/5000:ℝ)
        · exact Cell0130.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0131.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (1617/10000:ℝ)
      · by_cases h6 : a ≤ (101/625:ℝ)
        · exact Cell0132.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0133.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (809/5000:ℝ)
        · exact Cell0134.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0135.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (203/1250:ℝ)
    · by_cases h9 : a ≤ (1621/10000:ℝ)
      · by_cases h10 : a ≤ (81/500:ℝ)
        · exact Cell0136.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0137.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (811/5000:ℝ)
        · exact Cell0138.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0139.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (407/2500:ℝ)
      · by_cases h13 : a ≤ (813/5000:ℝ)
        · exact Cell0140.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0141.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (163/1000:ℝ)
        · exact Cell0142.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0143.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

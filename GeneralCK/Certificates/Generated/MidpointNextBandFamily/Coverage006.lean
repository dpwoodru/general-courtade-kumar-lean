import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0096
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0097
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0098
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0099
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0100
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0101
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0102
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0103
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0104
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0105
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0106
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0107
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0108
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0109
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0110
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0111
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage006 {a z : ℝ} (ha : Bounds (399/2500) (407/2500) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (403/2500:ℝ)
  · by_cases h1 : a ≤ (401/2500:ℝ)
    · by_cases h2 : a ≤ (4/25:ℝ)
      · by_cases h3 : a ≤ (799/5000:ℝ)
        · exact Cell0096.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0097.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (801/5000:ℝ)
        · exact Cell0098.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0099.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (201/1250:ℝ)
      · by_cases h6 : a ≤ (803/5000:ℝ)
        · exact Cell0100.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0101.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (161/1000:ℝ)
        · exact Cell0102.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0103.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (81/500:ℝ)
    · by_cases h9 : a ≤ (101/625:ℝ)
      · by_cases h10 : a ≤ (807/5000:ℝ)
        · exact Cell0104.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0105.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (809/5000:ℝ)
        · exact Cell0106.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0107.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (203/1250:ℝ)
      · by_cases h13 : a ≤ (811/5000:ℝ)
        · exact Cell0108.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0109.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (813/5000:ℝ)
        · exact Cell0110.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0111.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

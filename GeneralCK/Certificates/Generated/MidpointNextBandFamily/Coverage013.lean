import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0208
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0209
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0210
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0211
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0212
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0213
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0214
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0215
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0216
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0217
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0218
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0219
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0220
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0221
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0222
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0223
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage013 {a z : ℝ} (ha : Bounds (117/625) (39/200) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (119/625:ℝ)
  · by_cases h1 : a ≤ (118/625:ℝ)
    · by_cases h2 : a ≤ (47/250:ℝ)
      · by_cases h3 : a ≤ (469/2500:ℝ)
        · exact Cell0208.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0209.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (471/2500:ℝ)
        · exact Cell0210.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0211.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (237/1250:ℝ)
      · by_cases h6 : a ≤ (473/2500:ℝ)
        · exact Cell0212.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0213.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (19/100:ℝ)
        · exact Cell0214.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0215.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (963/5000:ℝ)
    · by_cases h9 : a ≤ (957/5000:ℝ)
      · by_cases h10 : a ≤ (477/2500:ℝ)
        · exact Cell0216.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0217.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (24/125:ℝ)
        · exact Cell0218.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0219.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (969/5000:ℝ)
      · by_cases h13 : a ≤ (483/2500:ℝ)
        · exact Cell0220.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0221.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (243/1250:ℝ)
        · exact Cell0222.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0223.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

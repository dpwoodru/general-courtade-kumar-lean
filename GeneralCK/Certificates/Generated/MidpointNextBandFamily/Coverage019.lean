import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0304
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0305
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0306
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0307
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0308
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0309
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0310
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0311
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0312
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0313
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0314
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0315
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0316
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0317
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0318
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0319
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage019 {a z : ℝ} (ha : Bounds (109/400) (79/250) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (117/400:ℝ)
  · by_cases h1 : a ≤ (141/500:ℝ)
    · by_cases h2 : a ≤ (277/1000:ℝ)
      · by_cases h3 : a ≤ (549/2000:ℝ)
        · exact Cell0304.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0305.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (559/2000:ℝ)
        · exact Cell0306.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0307.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (287/1000:ℝ)
      · by_cases h6 : a ≤ (569/2000:ℝ)
        · exact Cell0308.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0309.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (579/2000:ℝ)
        · exact Cell0310.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0311.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (38/125:ℝ)
    · by_cases h9 : a ≤ (597/2000:ℝ)
      · by_cases h10 : a ≤ (591/2000:ℝ)
        · exact Cell0312.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0313.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (301/1000:ℝ)
        · exact Cell0314.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0315.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (31/100:ℝ)
      · by_cases h13 : a ≤ (307/1000:ℝ)
        · exact Cell0316.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0317.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (313/1000:ℝ)
        · exact Cell0318.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0319.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

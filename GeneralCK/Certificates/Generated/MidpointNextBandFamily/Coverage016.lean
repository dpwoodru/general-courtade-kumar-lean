import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0256
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0257
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0258
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0259
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0260
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0261
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0262
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0263
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0264
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0265
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0266
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0267
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0268
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0269
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0270
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0271
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage016 {a z : ℝ} (ha : Bounds (53/250) (113/500) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (109/500:ℝ)
  · by_cases h1 : a ≤ (107/500:ℝ)
    · by_cases h2 : a ≤ (213/1000:ℝ)
      · by_cases h3 : a ≤ (17/80:ℝ)
        · exact Cell0256.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0257.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (427/2000:ℝ)
        · exact Cell0258.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0259.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (27/125:ℝ)
      · by_cases h6 : a ≤ (43/200:ℝ)
        · exact Cell0260.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0261.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (217/1000:ℝ)
        · exact Cell0262.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0263.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (111/500:ℝ)
    · by_cases h9 : a ≤ (11/50:ℝ)
      · by_cases h10 : a ≤ (219/1000:ℝ)
        · exact Cell0264.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0265.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (221/1000:ℝ)
        · exact Cell0266.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0267.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (28/125:ℝ)
      · by_cases h13 : a ≤ (223/1000:ℝ)
        · exact Cell0268.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0269.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (9/40:ℝ)
        · exact Cell0270.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0271.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

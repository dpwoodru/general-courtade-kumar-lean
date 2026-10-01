import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0336
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0337
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0338
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0339
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0340
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0341
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0342
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0343
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0344
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0345
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0346
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0347
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0348
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0349
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0350
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0351
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage021 {a z : ℝ} (ha : Bounds (393/1000) (141/250) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (459/1000:ℝ)
  · by_cases h1 : a ≤ (423/1000:ℝ)
    · by_cases h2 : a ≤ (407/1000:ℝ)
      · by_cases h3 : a ≤ (2/5:ℝ)
        · exact Cell0336.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0337.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (83/200:ℝ)
        · exact Cell0338.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0339.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (11/25:ℝ)
      · by_cases h6 : a ≤ (431/1000:ℝ)
        · exact Cell0340.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0341.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (449/1000:ℝ)
        · exact Cell0342.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0343.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (253/500:ℝ)
    · by_cases h9 : a ≤ (481/1000:ℝ)
      · by_cases h10 : a ≤ (47/100:ℝ)
        · exact Cell0344.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0345.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (493/1000:ℝ)
        · exact Cell0346.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0347.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (267/500:ℝ)
      · by_cases h13 : a ≤ (13/25:ℝ)
        · exact Cell0348.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0349.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (137/250:ℝ)
        · exact Cell0350.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0351.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

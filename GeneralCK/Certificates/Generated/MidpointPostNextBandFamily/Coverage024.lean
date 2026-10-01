import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0384
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0385
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0386
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0387
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0388
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0389
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0390
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0391
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0392
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0393
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0394
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0395
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0396
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0397
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0398
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0399
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage024 {a z : ℝ} (ha : Bounds (87/200) (82/125) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (259/500:ℝ)
  · by_cases h1 : a ≤ (19/40:ℝ)
    · by_cases h2 : a ≤ (227/500:ℝ)
      · by_cases h3 : a ≤ (111/250:ℝ)
        · exact Cell0384.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0385.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (58/125:ℝ)
        · exact Cell0386.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0387.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (247/500:ℝ)
      · by_cases h6 : a ≤ (243/500:ℝ)
        · exact Cell0388.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0389.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (253/500:ℝ)
        · exact Cell0390.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0391.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (289/500:ℝ)
    · by_cases h9 : a ≤ (273/500:ℝ)
      · by_cases h10 : a ≤ (133/250:ℝ)
        · exact Cell0392.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0393.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (281/500:ℝ)
        · exact Cell0394.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0395.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (307/500:ℝ)
      · by_cases h13 : a ≤ (149/250:ℝ)
        · exact Cell0396.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0397.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (317/500:ℝ)
        · exact Cell0398.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0399.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

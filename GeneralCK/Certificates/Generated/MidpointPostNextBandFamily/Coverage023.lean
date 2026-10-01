import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0368
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0369
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0370
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0371
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0372
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0373
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0374
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0375
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0376
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0377
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0378
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0379
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0380
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0381
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0382
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0383
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage023 {a z : ℝ} (ha : Bounds (169/500) (87/200) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (377/1000:ℝ)
  · by_cases h1 : a ≤ (89/250:ℝ)
    · by_cases h2 : a ≤ (173/500:ℝ)
      · by_cases h3 : a ≤ (171/500:ℝ)
        · exact Cell0368.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0369.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (351/1000:ℝ)
        · exact Cell0370.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0371.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (183/500:ℝ)
      · by_cases h6 : a ≤ (361/1000:ℝ)
        · exact Cell0372.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0373.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (371/1000:ℝ)
        · exact Cell0374.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0375.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (403/1000:ℝ)
    · by_cases h9 : a ≤ (389/1000:ℝ)
      · by_cases h10 : a ≤ (383/1000:ℝ)
        · exact Cell0376.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0377.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (99/250:ℝ)
        · exact Cell0378.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0379.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (209/500:ℝ)
      · by_cases h13 : a ≤ (41/100:ℝ)
        · exact Cell0380.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0381.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (213/500:ℝ)
        · exact Cell0382.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0383.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

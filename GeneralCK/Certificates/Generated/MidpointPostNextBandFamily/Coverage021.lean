import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0336
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0337
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0338
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0339
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0340
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0341
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0342
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0343
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0344
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0345
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0346
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0347
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0348
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0349
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0350
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0351
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage021 {a z : ℝ} (ha : Bounds (511/2000) (289/1000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (541/2000:ℝ)
  · by_cases h1 : a ≤ (21/80:ℝ)
    · by_cases h2 : a ≤ (517/2000:ℝ)
      · by_cases h3 : a ≤ (257/1000:ℝ)
        · exact Cell0336.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0337.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (521/2000:ℝ)
        · exact Cell0338.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0339.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (533/2000:ℝ)
      · by_cases h6 : a ≤ (529/2000:ℝ)
        · exact Cell0340.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0341.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (537/2000:ℝ)
        · exact Cell0342.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0343.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (279/1000:ℝ)
    · by_cases h9 : a ≤ (549/2000:ℝ)
      · by_cases h10 : a ≤ (109/400:ℝ)
        · exact Cell0344.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0345.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (553/2000:ℝ)
        · exact Cell0346.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0347.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (71/250:ℝ)
      · by_cases h13 : a ≤ (563/2000:ℝ)
        · exact Cell0348.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0349.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (573/2000:ℝ)
        · exact Cell0350.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0351.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

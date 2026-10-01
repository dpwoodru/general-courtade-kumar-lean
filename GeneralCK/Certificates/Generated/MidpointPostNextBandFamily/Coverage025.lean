import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0400
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0401
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0402
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0403
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0404
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0405
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0406
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0407
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0408
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0409
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0410
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0411
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage025 {a z : ℝ} (ha : Bounds (82/125) (999/1000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (83/100:ℝ)
  · by_cases h1 : a ≤ (367/500:ℝ)
    · by_cases h2 : a ≤ (17/25:ℝ)
      · exact Cell0400.curvature_pos ⟨ha.1,h2⟩ hz
      · by_cases h3 : a ≤ (353/500:ℝ)
        · exact Cell0401.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h3⟩ hz
        · exact Cell0402.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h1⟩ hz
    · by_cases h4 : a ≤ (191/250:ℝ)
      · exact Cell0403.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h4⟩ hz
      · by_cases h5 : a ≤ (199/250:ℝ)
        · exact Cell0404.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h5⟩ hz
        · exact Cell0405.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h0⟩ hz
  · by_cases h6 : a ≤ (47/50:ℝ)
    · by_cases h7 : a ≤ (173/200:ℝ)
      · exact Cell0406.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h7⟩ hz
      · by_cases h8 : a ≤ (9/10:ℝ)
        · exact Cell0407.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h8⟩ hz
        · exact Cell0408.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h6⟩ hz
    · by_cases h9 : a ≤ (489/500:ℝ)
      · exact Cell0409.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h9⟩ hz
      · by_cases h10 : a ≤ (499/500:ℝ)
        · exact Cell0410.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h10⟩ hz
        · exact Cell0411.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

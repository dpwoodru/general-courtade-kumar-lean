import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0224
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0225
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0226
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0227
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0228
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0229
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0230
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0231
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0232
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0233
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0234
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0235
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0236
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0237
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0238
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0239
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage014 {a z : ℝ} (ha : Bounds (897/5000) (929/5000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (913/5000:ℝ)
  · by_cases h1 : a ≤ (181/1000:ℝ)
    · by_cases h2 : a ≤ (901/5000:ℝ)
      · by_cases h3 : a ≤ (899/5000:ℝ)
        · exact Cell0224.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0225.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (903/5000:ℝ)
        · exact Cell0226.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0227.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (909/5000:ℝ)
      · by_cases h6 : a ≤ (907/5000:ℝ)
        · exact Cell0228.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0229.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (911/5000:ℝ)
        · exact Cell0230.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0231.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (921/5000:ℝ)
    · by_cases h9 : a ≤ (917/5000:ℝ)
      · by_cases h10 : a ≤ (183/1000:ℝ)
        · exact Cell0232.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0233.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (919/5000:ℝ)
        · exact Cell0234.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0235.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (37/200:ℝ)
      · by_cases h13 : a ≤ (923/5000:ℝ)
        · exact Cell0236.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0237.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (927/5000:ℝ)
        · exact Cell0238.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0239.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

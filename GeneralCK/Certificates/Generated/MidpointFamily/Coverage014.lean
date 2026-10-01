import GeneralCK.Certificates.Generated.MidpointFamily.Cell0224
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0225
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0226
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0227
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0228
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0229
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0230
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0231
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0232
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0233
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0234
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0235
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0236
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0237
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0238
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0239
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage014 {a z : ℝ} (ha : Bounds (487/2500) (99/500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(491/2500:ℝ)
  · by_cases h1 : a≤(489/2500:ℝ)
    · by_cases h2 : a≤(122/625:ℝ)
      · by_cases h3 : a≤(39/200:ℝ)
        · exact Cell0224.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0225.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(977/5000:ℝ)
        · exact Cell0226.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0227.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(49/250:ℝ)
      · by_cases h6 : a≤(979/5000:ℝ)
        · exact Cell0228.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0229.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(981/5000:ℝ)
        · exact Cell0230.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0231.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(493/2500:ℝ)
    · by_cases h9 : a≤(123/625:ℝ)
      · by_cases h10 : a≤(983/5000:ℝ)
        · exact Cell0232.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0233.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(197/1000:ℝ)
        · exact Cell0234.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0235.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(247/1250:ℝ)
      · by_cases h13 : a≤(987/5000:ℝ)
        · exact Cell0236.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0237.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(989/5000:ℝ)
        · exact Cell0238.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0239.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

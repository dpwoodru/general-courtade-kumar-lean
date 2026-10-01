import GeneralCK.Certificates.Generated.MidpointFamily.Cell0192
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0193
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0194
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0195
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0196
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0197
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0198
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0199
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0200
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0201
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0202
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0203
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0204
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0205
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0206
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0207
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage012 {a z : ℝ} (ha : Bounds (471/2500) (479/2500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(19/100:ℝ)
  · by_cases h1 : a≤(473/2500:ℝ)
    · by_cases h2 : a≤(118/625:ℝ)
      · by_cases h3 : a≤(943/5000:ℝ)
        · exact Cell0192.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0193.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(189/1000:ℝ)
        · exact Cell0194.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0195.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(237/1250:ℝ)
      · by_cases h6 : a≤(947/5000:ℝ)
        · exact Cell0196.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0197.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(949/5000:ℝ)
        · exact Cell0198.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0199.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(477/2500:ℝ)
    · by_cases h9 : a≤(119/625:ℝ)
      · by_cases h10 : a≤(951/5000:ℝ)
        · exact Cell0200.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0201.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(953/5000:ℝ)
        · exact Cell0202.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0203.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(239/1250:ℝ)
      · by_cases h13 : a≤(191/1000:ℝ)
        · exact Cell0204.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0205.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(957/5000:ℝ)
        · exact Cell0206.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0207.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

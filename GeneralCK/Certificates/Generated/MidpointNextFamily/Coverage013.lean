import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0208
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0209
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0210
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0211
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0212
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0213
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0214
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0215
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0216
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0217
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0218
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0219
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0220
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0221
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0222
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0223
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage013 {a z : ℝ} (ha : Bounds (479/2500) (487/2500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(483/2500:ℝ)
  · by_cases h1 : a≤(481/2500:ℝ)
    · by_cases h2 : a≤(24/125:ℝ)
      · by_cases h3 : a≤(959/5000:ℝ)
        · exact Cell0208.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0209.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(961/5000:ℝ)
        · exact Cell0210.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0211.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(241/1250:ℝ)
      · by_cases h6 : a≤(963/5000:ℝ)
        · exact Cell0212.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0213.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(193/1000:ℝ)
        · exact Cell0214.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0215.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(97/500:ℝ)
    · by_cases h9 : a≤(121/625:ℝ)
      · by_cases h10 : a≤(967/5000:ℝ)
        · exact Cell0216.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0217.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(969/5000:ℝ)
        · exact Cell0218.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0219.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(243/1250:ℝ)
      · by_cases h13 : a≤(971/5000:ℝ)
        · exact Cell0220.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0221.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(973/5000:ℝ)
        · exact Cell0222.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0223.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

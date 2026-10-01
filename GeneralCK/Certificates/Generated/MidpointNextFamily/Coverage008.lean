import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0128
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0129
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0130
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0131
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0132
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0133
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0134
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0135
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0136
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0137
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0138
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0139
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0140
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0141
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0142
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0143
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage008 {a z : ℝ} (ha : Bounds (439/2500) (447/2500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(443/2500:ℝ)
  · by_cases h1 : a≤(441/2500:ℝ)
    · by_cases h2 : a≤(22/125:ℝ)
      · by_cases h3 : a≤(879/5000:ℝ)
        · exact Cell0128.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0129.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(881/5000:ℝ)
        · exact Cell0130.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0131.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(221/1250:ℝ)
      · by_cases h6 : a≤(883/5000:ℝ)
        · exact Cell0132.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0133.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(177/1000:ℝ)
        · exact Cell0134.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0135.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(89/500:ℝ)
    · by_cases h9 : a≤(111/625:ℝ)
      · by_cases h10 : a≤(887/5000:ℝ)
        · exact Cell0136.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0137.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(889/5000:ℝ)
        · exact Cell0138.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0139.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(223/1250:ℝ)
      · by_cases h13 : a≤(891/5000:ℝ)
        · exact Cell0140.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0141.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(893/5000:ℝ)
        · exact Cell0142.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0143.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

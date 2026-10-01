import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0144
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0145
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0146
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0147
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0148
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0149
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0150
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0151
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0152
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0153
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0154
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0155
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0156
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0157
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0158
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0159
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage009 {a z : ℝ} (ha : Bounds (447/2500) (91/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(451/2500:ℝ)
  · by_cases h1 : a≤(449/2500:ℝ)
    · by_cases h2 : a≤(112/625:ℝ)
      · by_cases h3 : a≤(179/1000:ℝ)
        · exact Cell0144.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0145.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(897/5000:ℝ)
        · exact Cell0146.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0147.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(9/50:ℝ)
      · by_cases h6 : a≤(899/5000:ℝ)
        · exact Cell0148.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0149.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(901/5000:ℝ)
        · exact Cell0150.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0151.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(453/2500:ℝ)
    · by_cases h9 : a≤(113/625:ℝ)
      · by_cases h10 : a≤(903/5000:ℝ)
        · exact Cell0152.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0153.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(181/1000:ℝ)
        · exact Cell0154.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0155.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(227/1250:ℝ)
      · by_cases h13 : a≤(907/5000:ℝ)
        · exact Cell0156.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0157.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(909/5000:ℝ)
        · exact Cell0158.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0159.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

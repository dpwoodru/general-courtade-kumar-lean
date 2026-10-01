import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0256
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0257
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0258
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0259
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0260
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0261
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0262
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0263
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0264
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0265
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0266
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0267
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0268
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0269
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0270
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0271
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage016 {a z : ℝ} (ha : Bounds (203/1000) (211/1000) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(207/1000:ℝ)
  · by_cases h1 : a≤(41/200:ℝ)
    · by_cases h2 : a≤(51/250:ℝ)
      · by_cases h3 : a≤(407/2000:ℝ)
        · exact Cell0256.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0257.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(409/2000:ℝ)
        · exact Cell0258.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0259.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(103/500:ℝ)
      · by_cases h6 : a≤(411/2000:ℝ)
        · exact Cell0260.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0261.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(413/2000:ℝ)
        · exact Cell0262.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0263.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(209/1000:ℝ)
    · by_cases h9 : a≤(26/125:ℝ)
      · by_cases h10 : a≤(83/400:ℝ)
        · exact Cell0264.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0265.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(417/2000:ℝ)
        · exact Cell0266.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0267.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(21/100:ℝ)
      · by_cases h13 : a≤(419/2000:ℝ)
        · exact Cell0268.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0269.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(421/2000:ℝ)
        · exact Cell0270.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0271.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

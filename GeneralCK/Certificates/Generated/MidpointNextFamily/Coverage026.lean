import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0416
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0417
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0418
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0419
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0420
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0421
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0422
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0423
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0424
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0425
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0426
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0427
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0428
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0429
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0430
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0431
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage026 {a z : ℝ} (ha : Bounds (283/1000) (291/1000) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(287/1000:ℝ)
  · by_cases h1 : a≤(57/200:ℝ)
    · by_cases h2 : a≤(71/250:ℝ)
      · by_cases h3 : a≤(567/2000:ℝ)
        · exact Cell0416.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0417.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(569/2000:ℝ)
        · exact Cell0418.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0419.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(143/500:ℝ)
      · by_cases h6 : a≤(571/2000:ℝ)
        · exact Cell0420.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0421.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(573/2000:ℝ)
        · exact Cell0422.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0423.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(289/1000:ℝ)
    · by_cases h9 : a≤(36/125:ℝ)
      · by_cases h10 : a≤(23/80:ℝ)
        · exact Cell0424.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0425.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(577/2000:ℝ)
        · exact Cell0426.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0427.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(29/100:ℝ)
      · by_cases h13 : a≤(579/2000:ℝ)
        · exact Cell0428.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0429.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(581/2000:ℝ)
        · exact Cell0430.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0431.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0400
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0401
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0402
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0403
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0404
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0405
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0406
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0407
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0408
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0409
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0410
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0411
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0412
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0413
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0414
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0415
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage025 {a z : ℝ} (ha : Bounds (11/40) (283/1000) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(279/1000:ℝ)
  · by_cases h1 : a≤(277/1000:ℝ)
    · by_cases h2 : a≤(69/250:ℝ)
      · by_cases h3 : a≤(551/2000:ℝ)
        · exact Cell0400.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0401.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(553/2000:ℝ)
        · exact Cell0402.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0403.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(139/500:ℝ)
      · by_cases h6 : a≤(111/400:ℝ)
        · exact Cell0404.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0405.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(557/2000:ℝ)
        · exact Cell0406.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0407.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(281/1000:ℝ)
    · by_cases h9 : a≤(7/25:ℝ)
      · by_cases h10 : a≤(559/2000:ℝ)
        · exact Cell0408.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0409.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(561/2000:ℝ)
        · exact Cell0410.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0411.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(141/500:ℝ)
      · by_cases h13 : a≤(563/2000:ℝ)
        · exact Cell0412.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0413.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(113/400:ℝ)
        · exact Cell0414.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0415.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

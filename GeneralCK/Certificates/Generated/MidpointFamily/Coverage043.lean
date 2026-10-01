import GeneralCK.Certificates.Generated.MidpointFamily.Cell0688
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0689
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0690
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0691
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0692
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0693
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0694
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0695
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0696
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0697
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0698
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0699
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0700
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0701
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0702
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0703
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage043 {a z : ℝ} (ha : Bounds (72/125) (76/125) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(74/125:ℝ)
  · by_cases h1 : a≤(73/125:ℝ)
    · by_cases h2 : a≤(29/50:ℝ)
      · by_cases h3 : a≤(289/500:ℝ)
        · exact Cell0688.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0689.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(291/500:ℝ)
        · exact Cell0690.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0691.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(147/250:ℝ)
      · by_cases h6 : a≤(293/500:ℝ)
        · exact Cell0692.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0693.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(59/100:ℝ)
        · exact Cell0694.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0695.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(3/5:ℝ)
    · by_cases h9 : a≤(149/250:ℝ)
      · by_cases h10 : a≤(297/500:ℝ)
        · exact Cell0696.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0697.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(299/500:ℝ)
        · exact Cell0698.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0699.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(151/250:ℝ)
      · by_cases h13 : a≤(301/500:ℝ)
        · exact Cell0700.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0701.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(303/500:ℝ)
        · exact Cell0702.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0703.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

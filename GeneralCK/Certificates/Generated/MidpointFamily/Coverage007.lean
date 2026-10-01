import GeneralCK.Certificates.Generated.MidpointFamily.Cell0112
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0113
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0114
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0115
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0116
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0117
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0118
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0119
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0120
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0121
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0122
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0123
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0124
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0125
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0126
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0127
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage007 {a z : ℝ} (ha : Bounds (431/2500) (439/2500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(87/500:ℝ)
  · by_cases h1 : a≤(433/2500:ℝ)
    · by_cases h2 : a≤(108/625:ℝ)
      · by_cases h3 : a≤(863/5000:ℝ)
        · exact Cell0112.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0113.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(173/1000:ℝ)
        · exact Cell0114.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0115.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(217/1250:ℝ)
      · by_cases h6 : a≤(867/5000:ℝ)
        · exact Cell0116.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0117.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(869/5000:ℝ)
        · exact Cell0118.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0119.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(437/2500:ℝ)
    · by_cases h9 : a≤(109/625:ℝ)
      · by_cases h10 : a≤(871/5000:ℝ)
        · exact Cell0120.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0121.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(873/5000:ℝ)
        · exact Cell0122.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0123.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(219/1250:ℝ)
      · by_cases h13 : a≤(7/40:ℝ)
        · exact Cell0124.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0125.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(877/5000:ℝ)
        · exact Cell0126.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0127.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

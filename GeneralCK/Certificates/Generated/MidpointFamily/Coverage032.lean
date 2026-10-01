import GeneralCK.Certificates.Generated.MidpointFamily.Cell0512
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0513
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0514
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0515
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0516
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0517
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0518
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0519
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0520
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0521
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0522
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0523
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0524
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0525
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0526
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0527
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage032 {a z : ℝ} (ha : Bounds (181/500) (189/500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(37/100:ℝ)
  · by_cases h1 : a≤(183/500:ℝ)
    · by_cases h2 : a≤(91/250:ℝ)
      · by_cases h3 : a≤(363/1000:ℝ)
        · exact Cell0512.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0513.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(73/200:ℝ)
        · exact Cell0514.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0515.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(46/125:ℝ)
      · by_cases h6 : a≤(367/1000:ℝ)
        · exact Cell0516.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0517.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(369/1000:ℝ)
        · exact Cell0518.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0519.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(187/500:ℝ)
    · by_cases h9 : a≤(93/250:ℝ)
      · by_cases h10 : a≤(371/1000:ℝ)
        · exact Cell0520.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0521.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(373/1000:ℝ)
        · exact Cell0522.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0523.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(47/125:ℝ)
      · by_cases h13 : a≤(3/8:ℝ)
        · exact Cell0524.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0525.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(377/1000:ℝ)
        · exact Cell0526.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0527.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

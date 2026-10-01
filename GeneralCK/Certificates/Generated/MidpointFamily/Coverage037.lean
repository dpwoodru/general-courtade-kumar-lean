import GeneralCK.Certificates.Generated.MidpointFamily.Cell0592
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0593
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0594
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0595
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0596
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0597
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0598
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0599
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0600
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0601
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0602
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0603
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0604
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0605
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0606
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0607
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage037 {a z : ℝ} (ha : Bounds (221/500) (229/500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(9/20:ℝ)
  · by_cases h1 : a≤(223/500:ℝ)
    · by_cases h2 : a≤(111/250:ℝ)
      · by_cases h3 : a≤(443/1000:ℝ)
        · exact Cell0592.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0593.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(89/200:ℝ)
        · exact Cell0594.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0595.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(56/125:ℝ)
      · by_cases h6 : a≤(447/1000:ℝ)
        · exact Cell0596.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0597.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(449/1000:ℝ)
        · exact Cell0598.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0599.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(227/500:ℝ)
    · by_cases h9 : a≤(113/250:ℝ)
      · by_cases h10 : a≤(451/1000:ℝ)
        · exact Cell0600.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0601.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(453/1000:ℝ)
        · exact Cell0602.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0603.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(57/125:ℝ)
      · by_cases h13 : a≤(91/200:ℝ)
        · exact Cell0604.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0605.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(457/1000:ℝ)
        · exact Cell0606.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0607.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

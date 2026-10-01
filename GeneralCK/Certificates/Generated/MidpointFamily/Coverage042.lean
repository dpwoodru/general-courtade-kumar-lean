import GeneralCK.Certificates.Generated.MidpointFamily.Cell0672
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0673
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0674
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0675
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0676
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0677
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0678
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0679
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0680
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0681
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0682
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0683
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0684
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0685
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0686
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0687
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage042 {a z : ℝ} (ha : Bounds (68/125) (72/125) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(14/25:ℝ)
  · by_cases h1 : a≤(69/125:ℝ)
    · by_cases h2 : a≤(137/250:ℝ)
      · by_cases h3 : a≤(273/500:ℝ)
        · exact Cell0672.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0673.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(11/20:ℝ)
        · exact Cell0674.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0675.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(139/250:ℝ)
      · by_cases h6 : a≤(277/500:ℝ)
        · exact Cell0676.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0677.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(279/500:ℝ)
        · exact Cell0678.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0679.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(71/125:ℝ)
    · by_cases h9 : a≤(141/250:ℝ)
      · by_cases h10 : a≤(281/500:ℝ)
        · exact Cell0680.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0681.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(283/500:ℝ)
        · exact Cell0682.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0683.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(143/250:ℝ)
      · by_cases h13 : a≤(57/100:ℝ)
        · exact Cell0684.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0685.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(287/500:ℝ)
        · exact Cell0686.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0687.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

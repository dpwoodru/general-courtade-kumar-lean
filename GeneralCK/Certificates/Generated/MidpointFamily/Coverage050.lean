import GeneralCK.Certificates.Generated.MidpointFamily.Cell0800
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0801
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0802
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0803
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0804
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0805
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0806
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0807
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0808
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0809
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0810
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0811
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0812
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0813
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0814
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0815
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage050 {a z : ℝ} (ha : Bounds (4/5) (22/25) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(21/25:ℝ)
  · by_cases h1 : a≤(41/50:ℝ)
    · by_cases h2 : a≤(81/100:ℝ)
      · by_cases h3 : a≤(161/200:ℝ)
        · exact Cell0800.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0801.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(163/200:ℝ)
        · exact Cell0802.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0803.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(83/100:ℝ)
      · by_cases h6 : a≤(33/40:ℝ)
        · exact Cell0804.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0805.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(167/200:ℝ)
        · exact Cell0806.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0807.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(43/50:ℝ)
    · by_cases h9 : a≤(17/20:ℝ)
      · by_cases h10 : a≤(169/200:ℝ)
        · exact Cell0808.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0809.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(171/200:ℝ)
        · exact Cell0810.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0811.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(87/100:ℝ)
      · by_cases h13 : a≤(173/200:ℝ)
        · exact Cell0812.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0813.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(7/8:ℝ)
        · exact Cell0814.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0815.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

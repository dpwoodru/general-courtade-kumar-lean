import GeneralCK.Certificates.Generated.MidpointFamily.Cell0720
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0721
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0722
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0723
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0724
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0725
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0726
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0727
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0728
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0729
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0730
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0731
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0732
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0733
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0734
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0735
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage045 {a z : ℝ} (ha : Bounds (16/25) (84/125) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(82/125:ℝ)
  · by_cases h1 : a≤(81/125:ℝ)
    · by_cases h2 : a≤(161/250:ℝ)
      · by_cases h3 : a≤(321/500:ℝ)
        · exact Cell0720.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0721.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(323/500:ℝ)
        · exact Cell0722.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0723.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(163/250:ℝ)
      · by_cases h6 : a≤(13/20:ℝ)
        · exact Cell0724.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0725.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(327/500:ℝ)
        · exact Cell0726.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0727.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(83/125:ℝ)
    · by_cases h9 : a≤(33/50:ℝ)
      · by_cases h10 : a≤(329/500:ℝ)
        · exact Cell0728.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0729.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(331/500:ℝ)
        · exact Cell0730.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0731.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(167/250:ℝ)
      · by_cases h13 : a≤(333/500:ℝ)
        · exact Cell0732.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0733.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(67/100:ℝ)
        · exact Cell0734.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0735.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

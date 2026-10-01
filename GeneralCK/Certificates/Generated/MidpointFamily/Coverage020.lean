import GeneralCK.Certificates.Generated.MidpointFamily.Cell0320
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0321
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0322
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0323
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0324
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0325
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0326
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0327
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0328
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0329
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0330
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0331
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0332
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0333
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0334
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0335
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage020 {a z : ℝ} (ha : Bounds (47/200) (243/1000) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(239/1000:ℝ)
  · by_cases h1 : a≤(237/1000:ℝ)
    · by_cases h2 : a≤(59/250:ℝ)
      · by_cases h3 : a≤(471/2000:ℝ)
        · exact Cell0320.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0321.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(473/2000:ℝ)
        · exact Cell0322.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0323.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(119/500:ℝ)
      · by_cases h6 : a≤(19/80:ℝ)
        · exact Cell0324.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0325.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(477/2000:ℝ)
        · exact Cell0326.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0327.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(241/1000:ℝ)
    · by_cases h9 : a≤(6/25:ℝ)
      · by_cases h10 : a≤(479/2000:ℝ)
        · exact Cell0328.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0329.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(481/2000:ℝ)
        · exact Cell0330.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0331.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(121/500:ℝ)
      · by_cases h13 : a≤(483/2000:ℝ)
        · exact Cell0332.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0333.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(97/400:ℝ)
        · exact Cell0334.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0335.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

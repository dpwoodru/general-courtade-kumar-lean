import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0496
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0497
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0498
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0499
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0500
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0501
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0502
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0503
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0504
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0505
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0506
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0507
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0508
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0509
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0510
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0511
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage031 {a z : ℝ} (ha : Bounds (173/500) (181/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(177/500:ℝ)
  · by_cases h1 : a≤(7/20:ℝ)
    · by_cases h2 : a≤(87/250:ℝ)
      · by_cases h3 : a≤(347/1000:ℝ)
        · exact Cell0496.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0497.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(349/1000:ℝ)
        · exact Cell0498.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0499.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(44/125:ℝ)
      · by_cases h6 : a≤(351/1000:ℝ)
        · exact Cell0500.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0501.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(353/1000:ℝ)
        · exact Cell0502.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0503.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(179/500:ℝ)
    · by_cases h9 : a≤(89/250:ℝ)
      · by_cases h10 : a≤(71/200:ℝ)
        · exact Cell0504.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0505.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(357/1000:ℝ)
        · exact Cell0506.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0507.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(9/25:ℝ)
      · by_cases h13 : a≤(359/1000:ℝ)
        · exact Cell0508.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0509.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(361/1000:ℝ)
        · exact Cell0510.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0511.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0704
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0705
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0706
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0707
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0708
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0709
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0710
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0711
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0712
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0713
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0714
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0715
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0716
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0717
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0718
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0719
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage044 {a z : ℝ} (ha : Bounds (76/125) (16/25) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(78/125:ℝ)
  · by_cases h1 : a≤(77/125:ℝ)
    · by_cases h2 : a≤(153/250:ℝ)
      · by_cases h3 : a≤(61/100:ℝ)
        · exact Cell0704.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0705.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(307/500:ℝ)
        · exact Cell0706.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0707.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(31/50:ℝ)
      · by_cases h6 : a≤(309/500:ℝ)
        · exact Cell0708.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0709.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(311/500:ℝ)
        · exact Cell0710.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0711.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(79/125:ℝ)
    · by_cases h9 : a≤(157/250:ℝ)
      · by_cases h10 : a≤(313/500:ℝ)
        · exact Cell0712.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0713.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(63/100:ℝ)
        · exact Cell0714.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0715.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(159/250:ℝ)
      · by_cases h13 : a≤(317/500:ℝ)
        · exact Cell0716.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0717.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(319/500:ℝ)
        · exact Cell0718.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0719.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

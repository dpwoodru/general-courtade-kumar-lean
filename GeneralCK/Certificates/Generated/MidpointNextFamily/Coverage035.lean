import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0560
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0561
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0562
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0563
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0564
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0565
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0566
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0567
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0568
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0569
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0570
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0571
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0572
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0573
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0574
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0575
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage035 {a z : ℝ} (ha : Bounds (41/100) (213/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(209/500:ℝ)
  · by_cases h1 : a≤(207/500:ℝ)
    · by_cases h2 : a≤(103/250:ℝ)
      · by_cases h3 : a≤(411/1000:ℝ)
        · exact Cell0560.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0561.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(413/1000:ℝ)
        · exact Cell0562.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0563.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(52/125:ℝ)
      · by_cases h6 : a≤(83/200:ℝ)
        · exact Cell0564.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0565.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(417/1000:ℝ)
        · exact Cell0566.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0567.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(211/500:ℝ)
    · by_cases h9 : a≤(21/50:ℝ)
      · by_cases h10 : a≤(419/1000:ℝ)
        · exact Cell0568.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0569.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(421/1000:ℝ)
        · exact Cell0570.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0571.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(53/125:ℝ)
      · by_cases h13 : a≤(423/1000:ℝ)
        · exact Cell0572.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0573.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(17/40:ℝ)
        · exact Cell0574.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0575.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

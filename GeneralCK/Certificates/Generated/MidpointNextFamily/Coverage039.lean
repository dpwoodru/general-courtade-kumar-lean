import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0624
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0625
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0626
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0627
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0628
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0629
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0630
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0631
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0632
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0633
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0634
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0635
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0636
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0637
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0638
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0639
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage039 {a z : ℝ} (ha : Bounds (237/500) (49/100) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(241/500:ℝ)
  · by_cases h1 : a≤(239/500:ℝ)
    · by_cases h2 : a≤(119/250:ℝ)
      · by_cases h3 : a≤(19/40:ℝ)
        · exact Cell0624.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0625.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(477/1000:ℝ)
        · exact Cell0626.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0627.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(12/25:ℝ)
      · by_cases h6 : a≤(479/1000:ℝ)
        · exact Cell0628.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0629.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(481/1000:ℝ)
        · exact Cell0630.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0631.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(243/500:ℝ)
    · by_cases h9 : a≤(121/250:ℝ)
      · by_cases h10 : a≤(483/1000:ℝ)
        · exact Cell0632.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0633.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(97/200:ℝ)
        · exact Cell0634.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0635.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(61/125:ℝ)
      · by_cases h13 : a≤(487/1000:ℝ)
        · exact Cell0636.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0637.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(489/1000:ℝ)
        · exact Cell0638.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0639.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0576
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0577
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0578
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0579
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0580
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0581
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0582
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0583
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0584
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0585
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0586
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0587
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0588
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0589
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0590
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0591
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage036 {a z : ℝ} (ha : Bounds (213/500) (221/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(217/500:ℝ)
  · by_cases h1 : a≤(43/100:ℝ)
    · by_cases h2 : a≤(107/250:ℝ)
      · by_cases h3 : a≤(427/1000:ℝ)
        · exact Cell0576.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0577.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(429/1000:ℝ)
        · exact Cell0578.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0579.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(54/125:ℝ)
      · by_cases h6 : a≤(431/1000:ℝ)
        · exact Cell0580.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0581.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(433/1000:ℝ)
        · exact Cell0582.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0583.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(219/500:ℝ)
    · by_cases h9 : a≤(109/250:ℝ)
      · by_cases h10 : a≤(87/200:ℝ)
        · exact Cell0584.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0585.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(437/1000:ℝ)
        · exact Cell0586.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0587.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(11/25:ℝ)
      · by_cases h13 : a≤(439/1000:ℝ)
        · exact Cell0588.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0589.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(441/1000:ℝ)
        · exact Cell0590.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0591.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

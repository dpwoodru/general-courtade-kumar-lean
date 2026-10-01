import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0656
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0657
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0658
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0659
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0660
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0661
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0662
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0663
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0664
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0665
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0666
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0667
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0668
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0669
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0670
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0671
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage041 {a z : ℝ} (ha : Bounds (64/125) (68/125) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(66/125:ℝ)
  · by_cases h1 : a≤(13/25:ℝ)
    · by_cases h2 : a≤(129/250:ℝ)
      · by_cases h3 : a≤(257/500:ℝ)
        · exact Cell0656.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0657.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(259/500:ℝ)
        · exact Cell0658.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0659.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(131/250:ℝ)
      · by_cases h6 : a≤(261/500:ℝ)
        · exact Cell0660.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0661.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(263/500:ℝ)
        · exact Cell0662.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0663.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(67/125:ℝ)
    · by_cases h9 : a≤(133/250:ℝ)
      · by_cases h10 : a≤(53/100:ℝ)
        · exact Cell0664.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0665.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(267/500:ℝ)
        · exact Cell0666.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0667.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(27/50:ℝ)
      · by_cases h13 : a≤(269/500:ℝ)
        · exact Cell0668.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0669.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(271/500:ℝ)
        · exact Cell0670.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0671.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

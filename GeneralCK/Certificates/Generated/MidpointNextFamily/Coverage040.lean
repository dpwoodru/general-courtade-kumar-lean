import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0640
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0641
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0642
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0643
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0644
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0645
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0646
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0647
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0648
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0649
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0650
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0651
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0652
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0653
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0654
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0655
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage040 {a z : ℝ} (ha : Bounds (49/100) (64/125) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(249/500:ℝ)
  · by_cases h1 : a≤(247/500:ℝ)
    · by_cases h2 : a≤(123/250:ℝ)
      · by_cases h3 : a≤(491/1000:ℝ)
        · exact Cell0640.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0641.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(493/1000:ℝ)
        · exact Cell0642.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0643.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(62/125:ℝ)
      · by_cases h6 : a≤(99/200:ℝ)
        · exact Cell0644.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0645.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(497/1000:ℝ)
        · exact Cell0646.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0647.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(63/125:ℝ)
    · by_cases h9 : a≤(1/2:ℝ)
      · by_cases h10 : a≤(499/1000:ℝ)
        · exact Cell0648.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0649.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(251/500:ℝ)
        · exact Cell0650.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0651.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(127/250:ℝ)
      · by_cases h13 : a≤(253/500:ℝ)
        · exact Cell0652.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0653.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(51/100:ℝ)
        · exact Cell0654.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0655.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

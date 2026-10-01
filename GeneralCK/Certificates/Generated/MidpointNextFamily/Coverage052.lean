import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0832
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0833
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0834
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0835
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0836
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0837
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0838
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0839
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0840
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0841
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0842
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0843
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0844
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0845
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0846
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0847
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage052 {a z : ℝ} (ha : Bounds (477/500) (493/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(97/100:ℝ)
  · by_cases h1 : a≤(481/500:ℝ)
    · by_cases h2 : a≤(479/500:ℝ)
      · by_cases h3 : a≤(239/250:ℝ)
        · exact Cell0832.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0833.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(24/25:ℝ)
        · exact Cell0834.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0835.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(483/500:ℝ)
      · by_cases h6 : a≤(241/250:ℝ)
        · exact Cell0836.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0837.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(121/125:ℝ)
        · exact Cell0838.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0839.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(489/500:ℝ)
    · by_cases h9 : a≤(487/500:ℝ)
      · by_cases h10 : a≤(243/250:ℝ)
        · exact Cell0840.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0841.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(122/125:ℝ)
        · exact Cell0842.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0843.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(491/500:ℝ)
      · by_cases h13 : a≤(49/50:ℝ)
        · exact Cell0844.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0845.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(123/125:ℝ)
        · exact Cell0846.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0847.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

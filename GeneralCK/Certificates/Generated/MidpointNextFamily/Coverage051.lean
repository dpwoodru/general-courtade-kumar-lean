import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0816
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0817
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0818
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0819
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0820
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0821
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0822
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0823
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0824
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0825
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0826
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0827
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0828
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0829
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0830
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0831
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage051 {a z : ℝ} (ha : Bounds (22/25) (477/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(23/25:ℝ)
  · by_cases h1 : a≤(9/10:ℝ)
    · by_cases h2 : a≤(89/100:ℝ)
      · by_cases h3 : a≤(177/200:ℝ)
        · exact Cell0816.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0817.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(179/200:ℝ)
        · exact Cell0818.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0819.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(91/100:ℝ)
      · by_cases h6 : a≤(181/200:ℝ)
        · exact Cell0820.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0821.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(183/200:ℝ)
        · exact Cell0822.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0823.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(47/50:ℝ)
    · by_cases h9 : a≤(93/100:ℝ)
      · by_cases h10 : a≤(37/40:ℝ)
        · exact Cell0824.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0825.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(187/200:ℝ)
        · exact Cell0826.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0827.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(19/20:ℝ)
      · by_cases h13 : a≤(189/200:ℝ)
        · exact Cell0828.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0829.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(119/125:ℝ)
        · exact Cell0830.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0831.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

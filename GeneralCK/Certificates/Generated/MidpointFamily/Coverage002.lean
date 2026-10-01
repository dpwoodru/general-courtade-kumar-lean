import GeneralCK.Certificates.Generated.MidpointFamily.Cell0032
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0033
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0034
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0035
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0036
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0037
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0038
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0039
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0040
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0041
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0042
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0043
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0044
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0045
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0046
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0047
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage002 {a z : ℝ} (ha : Bounds (391/2500) (399/2500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(79/500:ℝ)
  · by_cases h1 : a≤(393/2500:ℝ)
    · by_cases h2 : a≤(98/625:ℝ)
      · by_cases h3 : a≤(783/5000:ℝ)
        · exact Cell0032.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0033.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(157/1000:ℝ)
        · exact Cell0034.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0035.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(197/1250:ℝ)
      · by_cases h6 : a≤(787/5000:ℝ)
        · exact Cell0036.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0037.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(789/5000:ℝ)
        · exact Cell0038.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0039.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(397/2500:ℝ)
    · by_cases h9 : a≤(99/625:ℝ)
      · by_cases h10 : a≤(791/5000:ℝ)
        · exact Cell0040.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0041.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(793/5000:ℝ)
        · exact Cell0042.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0043.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(199/1250:ℝ)
      · by_cases h13 : a≤(159/1000:ℝ)
        · exact Cell0044.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0045.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(797/5000:ℝ)
        · exact Cell0046.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0047.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

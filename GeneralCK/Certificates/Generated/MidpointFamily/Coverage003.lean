import GeneralCK.Certificates.Generated.MidpointFamily.Cell0048
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0049
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0050
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0051
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0052
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0053
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0054
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0055
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0056
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0057
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0058
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0059
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0060
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0061
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0062
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0063
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage003 {a z : ℝ} (ha : Bounds (399/2500) (407/2500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(403/2500:ℝ)
  · by_cases h1 : a≤(401/2500:ℝ)
    · by_cases h2 : a≤(4/25:ℝ)
      · by_cases h3 : a≤(799/5000:ℝ)
        · exact Cell0048.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0049.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(801/5000:ℝ)
        · exact Cell0050.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0051.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(201/1250:ℝ)
      · by_cases h6 : a≤(803/5000:ℝ)
        · exact Cell0052.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0053.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(161/1000:ℝ)
        · exact Cell0054.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0055.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(81/500:ℝ)
    · by_cases h9 : a≤(101/625:ℝ)
      · by_cases h10 : a≤(807/5000:ℝ)
        · exact Cell0056.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0057.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(809/5000:ℝ)
        · exact Cell0058.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0059.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(203/1250:ℝ)
      · by_cases h13 : a≤(811/5000:ℝ)
        · exact Cell0060.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0061.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(813/5000:ℝ)
        · exact Cell0062.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0063.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

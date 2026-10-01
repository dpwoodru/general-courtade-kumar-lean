import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0016
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0017
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0018
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0019
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0020
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0021
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0022
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0023
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0024
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0025
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0026
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0027
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0028
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0029
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0030
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0031
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage001 {a z : ℝ} (ha : Bounds (383/2500) (391/2500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(387/2500:ℝ)
  · by_cases h1 : a≤(77/500:ℝ)
    · by_cases h2 : a≤(96/625:ℝ)
      · by_cases h3 : a≤(767/5000:ℝ)
        · exact Cell0016.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0017.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(769/5000:ℝ)
        · exact Cell0018.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0019.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(193/1250:ℝ)
      · by_cases h6 : a≤(771/5000:ℝ)
        · exact Cell0020.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0021.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(773/5000:ℝ)
        · exact Cell0022.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0023.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(389/2500:ℝ)
    · by_cases h9 : a≤(97/625:ℝ)
      · by_cases h10 : a≤(31/200:ℝ)
        · exact Cell0024.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0025.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(777/5000:ℝ)
        · exact Cell0026.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0027.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(39/250:ℝ)
      · by_cases h13 : a≤(779/5000:ℝ)
        · exact Cell0028.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0029.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(781/5000:ℝ)
        · exact Cell0030.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0031.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

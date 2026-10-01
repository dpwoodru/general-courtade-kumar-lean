import GeneralCK.Certificates.Generated.MidpointFamily.Cell0736
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0737
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0738
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0739
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0740
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0741
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0742
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0743
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0744
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0745
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0746
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0747
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0748
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0749
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0750
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0751
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage046 {a z : ℝ} (ha : Bounds (84/125) (88/125) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(86/125:ℝ)
  · by_cases h1 : a≤(17/25:ℝ)
    · by_cases h2 : a≤(169/250:ℝ)
      · by_cases h3 : a≤(337/500:ℝ)
        · exact Cell0736.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0737.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(339/500:ℝ)
        · exact Cell0738.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0739.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(171/250:ℝ)
      · by_cases h6 : a≤(341/500:ℝ)
        · exact Cell0740.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0741.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(343/500:ℝ)
        · exact Cell0742.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0743.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(87/125:ℝ)
    · by_cases h9 : a≤(173/250:ℝ)
      · by_cases h10 : a≤(69/100:ℝ)
        · exact Cell0744.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0745.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(347/500:ℝ)
        · exact Cell0746.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0747.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(7/10:ℝ)
      · by_cases h13 : a≤(349/500:ℝ)
        · exact Cell0748.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0749.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(351/500:ℝ)
        · exact Cell0750.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0751.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

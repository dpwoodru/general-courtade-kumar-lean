import GeneralCK.Certificates.Generated.MidpointFamily.Cell0848
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0849
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0850
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0851
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0852
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0853
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0854
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0855
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0856
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0857
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0858
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage053 {a z : ℝ} (ha : Bounds (493/500) (999/1000) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(993/1000:ℝ)
  · by_cases h1 : a≤(99/100:ℝ)
    · by_cases h2 : a≤(247/250:ℝ)
      · exact Cell0848.curvature_pos ⟨ha.1,h2⟩ hz
      · exact Cell0849.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h1⟩ hz
    · by_cases h3 : a≤(991/1000:ℝ)
      · exact Cell0850.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h3⟩ hz
      · by_cases h4 : a≤(124/125:ℝ)
        · exact Cell0851.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h4⟩ hz
        · exact Cell0852.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h0⟩ hz
  · by_cases h5 : a≤(249/250:ℝ)
    · by_cases h6 : a≤(497/500:ℝ)
      · exact Cell0853.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h6⟩ hz
      · by_cases h7 : a≤(199/200:ℝ)
        · exact Cell0854.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h7⟩ hz
        · exact Cell0855.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h5⟩ hz
    · by_cases h8 : a≤(997/1000:ℝ)
      · exact Cell0856.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h8⟩ hz
      · by_cases h9 : a≤(499/500:ℝ)
        · exact Cell0857.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h9⟩ hz
        · exact Cell0858.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

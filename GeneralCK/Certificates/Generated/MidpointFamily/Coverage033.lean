import GeneralCK.Certificates.Generated.MidpointFamily.Cell0528
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0529
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0530
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0531
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0532
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0533
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0534
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0535
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0536
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0537
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0538
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0539
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0540
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0541
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0542
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0543
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage033 {a z : ℝ} (ha : Bounds (189/500) (197/500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(193/500:ℝ)
  · by_cases h1 : a≤(191/500:ℝ)
    · by_cases h2 : a≤(19/50:ℝ)
      · by_cases h3 : a≤(379/1000:ℝ)
        · exact Cell0528.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0529.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(381/1000:ℝ)
        · exact Cell0530.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0531.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(48/125:ℝ)
      · by_cases h6 : a≤(383/1000:ℝ)
        · exact Cell0532.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0533.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(77/200:ℝ)
        · exact Cell0534.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0535.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(39/100:ℝ)
    · by_cases h9 : a≤(97/250:ℝ)
      · by_cases h10 : a≤(387/1000:ℝ)
        · exact Cell0536.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0537.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(389/1000:ℝ)
        · exact Cell0538.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0539.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(49/125:ℝ)
      · by_cases h13 : a≤(391/1000:ℝ)
        · exact Cell0540.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0541.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(393/1000:ℝ)
        · exact Cell0542.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0543.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

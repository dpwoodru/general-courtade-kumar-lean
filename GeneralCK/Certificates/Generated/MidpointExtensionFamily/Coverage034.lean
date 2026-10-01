import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0534
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0535
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0536
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0537
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0538
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0539
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0540
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0541
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0542
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0543
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0544
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0545
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0546
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0547
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0548
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0549
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage034 {a z : ℝ} (ha : Bounds (223/500) (361/500) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (137/250:ℝ)
  · by_cases h1 : a ≤ (491/1000:ℝ)
    · by_cases h2 : a ≤ (467/1000:ℝ)
      · by_cases h3 : a ≤ (57/125:ℝ)
        · exact Cell0534.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0535.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (479/1000:ℝ)
        · exact Cell0536.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0537.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (259/500:ℝ)
      · by_cases h6 : a ≤ (63/125:ℝ)
        · exact Cell0538.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0539.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (133/250:ℝ)
        · exact Cell0540.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0541.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (311/500:ℝ)
    · by_cases h9 : a ≤ (291/500:ℝ)
      · by_cases h10 : a ≤ (141/250:ℝ)
        · exact Cell0542.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0543.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (301/500:ℝ)
        · exact Cell0544.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0545.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (167/250:ℝ)
      · by_cases h13 : a ≤ (161/250:ℝ)
        · exact Cell0546.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0547.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (347/500:ℝ)
        · exact Cell0548.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0549.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

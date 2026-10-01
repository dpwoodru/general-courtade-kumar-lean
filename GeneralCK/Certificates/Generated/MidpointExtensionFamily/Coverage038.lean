import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0591
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0592
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0593
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0594
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0595
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0596
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0597
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0598
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0599
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0600
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0601
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0602
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0603
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0604
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0605
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0606
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage038 {a z : ℝ} (ha : Bounds (779/5000) (159/1000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (787/5000:ℝ)
  · by_cases h1 : a ≤ (783/5000:ℝ)
    · by_cases h2 : a ≤ (781/5000:ℝ)
      · by_cases h3 : a ≤ (39/250:ℝ)
        · exact Cell0591.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0592.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (391/2500:ℝ)
        · exact Cell0593.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0594.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (157/1000:ℝ)
      · by_cases h6 : a ≤ (98/625:ℝ)
        · exact Cell0595.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0596.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (393/2500:ℝ)
        · exact Cell0597.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0598.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (791/5000:ℝ)
    · by_cases h9 : a ≤ (789/5000:ℝ)
      · by_cases h10 : a ≤ (197/1250:ℝ)
        · exact Cell0599.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0600.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (79/500:ℝ)
        · exact Cell0601.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0602.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (793/5000:ℝ)
      · by_cases h13 : a ≤ (99/625:ℝ)
        · exact Cell0603.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0604.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (397/2500:ℝ)
        · exact Cell0605.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0606.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0639
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0640
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0641
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0642
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0643
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0644
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0645
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0646
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0647
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0648
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0649
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0650
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0651
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0652
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0653
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0654
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage041 {a z : ℝ} (ha : Bounds (827/5000) (843/5000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (167/1000:ℝ)
  · by_cases h1 : a ≤ (831/5000:ℝ)
    · by_cases h2 : a ≤ (829/5000:ℝ)
      · by_cases h3 : a ≤ (207/1250:ℝ)
        · exact Cell0639.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0640.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (83/500:ℝ)
        · exact Cell0641.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0642.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (833/5000:ℝ)
      · by_cases h6 : a ≤ (104/625:ℝ)
        · exact Cell0643.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0644.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (417/2500:ℝ)
        · exact Cell0645.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0646.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (839/5000:ℝ)
    · by_cases h9 : a ≤ (837/5000:ℝ)
      · by_cases h10 : a ≤ (209/1250:ℝ)
        · exact Cell0647.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0648.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (419/2500:ℝ)
        · exact Cell0649.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0650.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (841/5000:ℝ)
      · by_cases h13 : a ≤ (21/125:ℝ)
        · exact Cell0651.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0652.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (421/2500:ℝ)
        · exact Cell0653.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0654.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

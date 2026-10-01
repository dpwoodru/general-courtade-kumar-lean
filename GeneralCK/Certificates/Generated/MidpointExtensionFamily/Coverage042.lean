import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0655
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0656
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0657
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0658
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0659
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0660
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0661
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0662
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0663
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0664
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0665
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0666
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0667
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0668
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0669
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0670
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage042 {a z : ℝ} (ha : Bounds (843/5000) (7/40) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (859/5000:ℝ)
  · by_cases h1 : a ≤ (851/5000:ℝ)
    · by_cases h2 : a ≤ (847/5000:ℝ)
      · by_cases h3 : a ≤ (169/1000:ℝ)
        · exact Cell0655.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0656.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (849/5000:ℝ)
        · exact Cell0657.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0658.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (171/1000:ℝ)
      · by_cases h6 : a ≤ (853/5000:ℝ)
        · exact Cell0659.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0660.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (857/5000:ℝ)
        · exact Cell0661.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0662.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (867/5000:ℝ)
    · by_cases h9 : a ≤ (863/5000:ℝ)
      · by_cases h10 : a ≤ (861/5000:ℝ)
        · exact Cell0663.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0664.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (173/1000:ℝ)
        · exact Cell0665.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0666.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (871/5000:ℝ)
      · by_cases h13 : a ≤ (869/5000:ℝ)
        · exact Cell0667.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0668.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (873/5000:ℝ)
        · exact Cell0669.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0670.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

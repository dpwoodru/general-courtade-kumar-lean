import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0735
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0736
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0737
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0738
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0739
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0740
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0741
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0742
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0743
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0744
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0745
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0746
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0747
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0748
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0749
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0750
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage047 {a z : ℝ} (ha : Bounds (421/2000) (453/2000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (437/2000:ℝ)
  · by_cases h1 : a ≤ (429/2000:ℝ)
    · by_cases h2 : a ≤ (17/80:ℝ)
      · by_cases h3 : a ≤ (423/2000:ℝ)
        · exact Cell0735.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0736.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (427/2000:ℝ)
        · exact Cell0737.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0738.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (433/2000:ℝ)
      · by_cases h6 : a ≤ (431/2000:ℝ)
        · exact Cell0739.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0740.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (87/400:ℝ)
        · exact Cell0741.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0742.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (89/400:ℝ)
    · by_cases h9 : a ≤ (441/2000:ℝ)
      · by_cases h10 : a ≤ (439/2000:ℝ)
        · exact Cell0743.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0744.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (443/2000:ℝ)
        · exact Cell0745.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0746.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (449/2000:ℝ)
      · by_cases h13 : a ≤ (447/2000:ℝ)
        · exact Cell0747.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0748.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (451/2000:ℝ)
        · exact Cell0749.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0750.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

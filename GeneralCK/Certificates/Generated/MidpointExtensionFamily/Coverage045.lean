import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0703
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0704
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0705
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0706
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0707
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0708
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0709
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0710
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0711
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0712
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0713
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0714
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0715
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0716
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0717
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0718
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage045 {a z : ℝ} (ha : Bounds (19/100) (401/2000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (487/2500:ℝ)
  · by_cases h1 : a ≤ (481/2500:ℝ)
    · by_cases h2 : a ≤ (239/1250:ℝ)
      · by_cases h3 : a ≤ (953/5000:ℝ)
        · exact Cell0703.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0704.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (959/5000:ℝ)
        · exact Cell0705.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0706.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (121/625:ℝ)
      · by_cases h6 : a ≤ (193/1000:ℝ)
        · exact Cell0707.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0708.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (971/5000:ℝ)
        · exact Cell0709.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0710.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (247/1250:ℝ)
    · by_cases h9 : a ≤ (49/250:ℝ)
      · by_cases h10 : a ≤ (977/5000:ℝ)
        · exact Cell0711.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0712.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (123/625:ℝ)
        · exact Cell0713.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0714.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (249/1250:ℝ)
      · by_cases h13 : a ≤ (124/625:ℝ)
        · exact Cell0715.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0716.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (1/5:ℝ)
        · exact Cell0717.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0718.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

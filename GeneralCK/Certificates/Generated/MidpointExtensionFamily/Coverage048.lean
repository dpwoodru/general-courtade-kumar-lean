import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0751
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0752
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0753
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0754
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0755
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0756
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0757
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0758
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0759
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0760
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0761
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0762
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0763
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0764
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0765
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0766
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage048 {a z : ℝ} (ha : Bounds (453/2000) (497/2000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (473/2000:ℝ)
  · by_cases h1 : a ≤ (461/2000:ℝ)
    · by_cases h2 : a ≤ (457/2000:ℝ)
      · by_cases h3 : a ≤ (91/400:ℝ)
        · exact Cell0751.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0752.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (459/2000:ℝ)
        · exact Cell0753.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0754.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (467/2000:ℝ)
      · by_cases h6 : a ≤ (29/125:ℝ)
        · exact Cell0755.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0756.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (47/200:ℝ)
        · exact Cell0757.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0758.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (97/400:ℝ)
    · by_cases h9 : a ≤ (479/2000:ℝ)
      · by_cases h10 : a ≤ (119/500:ℝ)
        · exact Cell0759.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0760.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (241/1000:ℝ)
        · exact Cell0761.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0762.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (491/2000:ℝ)
      · by_cases h13 : a ≤ (61/250:ℝ)
        · exact Cell0763.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0764.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (247/1000:ℝ)
        · exact Cell0765.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0766.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

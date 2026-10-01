import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0719
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0720
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0721
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0722
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0723
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0724
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0725
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0726
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0727
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0728
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0729
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0730
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0731
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0732
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0733
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0734
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage046 {a z : ℝ} (ha : Bounds (401/2000) (421/2000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (409/2000:ℝ)
  · by_cases h1 : a ≤ (81/400:ℝ)
    · by_cases h2 : a ≤ (403/2000:ℝ)
      · by_cases h3 : a ≤ (201/1000:ℝ)
        · exact Cell0719.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0720.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (101/500:ℝ)
        · exact Cell0721.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0722.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (407/2000:ℝ)
      · by_cases h6 : a ≤ (203/1000:ℝ)
        · exact Cell0723.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0724.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (51/250:ℝ)
        · exact Cell0725.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0726.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (413/2000:ℝ)
    · by_cases h9 : a ≤ (411/2000:ℝ)
      · by_cases h10 : a ≤ (41/200:ℝ)
        · exact Cell0727.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0728.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (103/500:ℝ)
        · exact Cell0729.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0730.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (417/2000:ℝ)
      · by_cases h13 : a ≤ (83/400:ℝ)
        · exact Cell0731.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0732.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (419/2000:ℝ)
        · exact Cell0733.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0734.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

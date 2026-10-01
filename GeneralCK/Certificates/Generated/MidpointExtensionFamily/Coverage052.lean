import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0815
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0816
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0817
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0818
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0819
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0820
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0821
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0822
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0823
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0824
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0825
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0826
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0827
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0828
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0829
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0830
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage052 {a z : ℝ} (ha : Bounds (223/500) (361/500) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (137/250:ℝ)
  · by_cases h1 : a ≤ (491/1000:ℝ)
    · by_cases h2 : a ≤ (467/1000:ℝ)
      · by_cases h3 : a ≤ (57/125:ℝ)
        · exact Cell0815.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0816.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (479/1000:ℝ)
        · exact Cell0817.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0818.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (259/500:ℝ)
      · by_cases h6 : a ≤ (63/125:ℝ)
        · exact Cell0819.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0820.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (133/250:ℝ)
        · exact Cell0821.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0822.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (311/500:ℝ)
    · by_cases h9 : a ≤ (291/500:ℝ)
      · by_cases h10 : a ≤ (141/250:ℝ)
        · exact Cell0823.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0824.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (301/500:ℝ)
        · exact Cell0825.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0826.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (167/250:ℝ)
      · by_cases h13 : a ≤ (161/250:ℝ)
        · exact Cell0827.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0828.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (347/500:ℝ)
        · exact Cell0829.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0830.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

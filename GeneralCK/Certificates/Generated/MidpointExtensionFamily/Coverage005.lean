import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0080
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0081
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0082
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0083
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0084
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0085
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0086
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0087
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0088
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0089
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0090
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0091
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0092
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0093
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0094
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0095
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage005 {a z : ℝ} (ha : Bounds (829/5000) (106/625) a)
    (hz : Bounds (1/20) (81/1000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (837/5000:ℝ)
  · by_cases h1 : a ≤ (833/5000:ℝ)
    · by_cases h2 : a ≤ (831/5000:ℝ)
      · by_cases h3 : a ≤ (83/500:ℝ)
        · exact Cell0080.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0081.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (104/625:ℝ)
        · exact Cell0082.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0083.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (167/1000:ℝ)
      · by_cases h6 : a ≤ (417/2500:ℝ)
        · exact Cell0084.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0085.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (209/1250:ℝ)
        · exact Cell0086.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0087.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (841/5000:ℝ)
    · by_cases h9 : a ≤ (839/5000:ℝ)
      · by_cases h10 : a ≤ (419/2500:ℝ)
        · exact Cell0088.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0089.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (21/125:ℝ)
        · exact Cell0090.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0091.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (211/1250:ℝ)
      · by_cases h13 : a ≤ (421/2500:ℝ)
        · exact Cell0092.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0093.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (423/2500:ℝ)
        · exact Cell0094.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0095.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

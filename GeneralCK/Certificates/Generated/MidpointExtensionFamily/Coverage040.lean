import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0623
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0624
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0625
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0626
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0627
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0628
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0629
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0630
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0631
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0632
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0633
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0634
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0635
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0636
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0637
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0638
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage040 {a z : ℝ} (ha : Bounds (811/5000) (827/5000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (819/5000:ℝ)
  · by_cases h1 : a ≤ (163/1000:ℝ)
    · by_cases h2 : a ≤ (813/5000:ℝ)
      · by_cases h3 : a ≤ (203/1250:ℝ)
        · exact Cell0623.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0624.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (407/2500:ℝ)
        · exact Cell0625.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0626.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (817/5000:ℝ)
      · by_cases h6 : a ≤ (102/625:ℝ)
        · exact Cell0627.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0628.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (409/2500:ℝ)
        · exact Cell0629.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0630.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (823/5000:ℝ)
    · by_cases h9 : a ≤ (821/5000:ℝ)
      · by_cases h10 : a ≤ (41/250:ℝ)
        · exact Cell0631.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0632.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (411/2500:ℝ)
        · exact Cell0633.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0634.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (33/200:ℝ)
      · by_cases h13 : a ≤ (103/625:ℝ)
        · exact Cell0635.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0636.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (413/2500:ℝ)
        · exact Cell0637.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0638.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

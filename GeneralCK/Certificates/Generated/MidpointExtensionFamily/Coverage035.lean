import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0550
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0551
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0552
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0553
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0554
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0555
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0556
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0557
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0558
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage035 {a z : ℝ} (ha : Bounds (361/500) (999/1000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (17/20:ℝ)
  · by_cases h1 : a ≤ (98/125:ℝ)
    · by_cases h2 : a ≤ (94/125:ℝ)
      · exact Cell0550.curvature_pos ⟨ha.1,h2⟩ hz
      · exact Cell0551.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h1⟩ hz
    · by_cases h3 : a ≤ (163/200:ℝ)
      · exact Cell0552.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h3⟩ hz
      · exact Cell0553.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h0⟩ hz
  · by_cases h4 : a ≤ (93/100:ℝ)
    · by_cases h5 : a ≤ (89/100:ℝ)
      · exact Cell0554.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h5⟩ hz
      · exact Cell0555.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h4⟩ hz
    · by_cases h6 : a ≤ (97/100:ℝ)
      · exact Cell0556.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h6⟩ hz
      · by_cases h7 : a ≤ (249/250:ℝ)
        · exact Cell0557.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h7⟩ hz
        · exact Cell0558.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

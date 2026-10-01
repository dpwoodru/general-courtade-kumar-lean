import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0342
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0343
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0344
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0345
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0346
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0347
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0348
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0349
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0350
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0351
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0352
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0353
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0354
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0355
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0356
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0357
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage022 {a z : ℝ} (ha : Bounds (811/5000) (827/5000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (819/5000:ℝ)
  · by_cases h1 : a ≤ (163/1000:ℝ)
    · by_cases h2 : a ≤ (813/5000:ℝ)
      · by_cases h3 : a ≤ (203/1250:ℝ)
        · exact Cell0342.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0343.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (407/2500:ℝ)
        · exact Cell0344.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0345.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (817/5000:ℝ)
      · by_cases h6 : a ≤ (102/625:ℝ)
        · exact Cell0346.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0347.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (409/2500:ℝ)
        · exact Cell0348.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0349.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (823/5000:ℝ)
    · by_cases h9 : a ≤ (821/5000:ℝ)
      · by_cases h10 : a ≤ (41/250:ℝ)
        · exact Cell0350.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0351.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (411/2500:ℝ)
        · exact Cell0352.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0353.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (33/200:ℝ)
      · by_cases h13 : a ≤ (103/625:ℝ)
        · exact Cell0354.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0355.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (413/2500:ℝ)
        · exact Cell0356.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0357.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

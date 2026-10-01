import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0326
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0327
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0328
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0329
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0330
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0331
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0332
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0333
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0334
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0335
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0336
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0337
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0338
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0339
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0340
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0341
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage021 {a z : ℝ} (ha : Bounds (159/1000) (811/5000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (803/5000:ℝ)
  · by_cases h1 : a ≤ (799/5000:ℝ)
    · by_cases h2 : a ≤ (797/5000:ℝ)
      · by_cases h3 : a ≤ (199/1250:ℝ)
        · exact Cell0326.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0327.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (399/2500:ℝ)
        · exact Cell0328.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0329.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (801/5000:ℝ)
      · by_cases h6 : a ≤ (4/25:ℝ)
        · exact Cell0330.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0331.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (401/2500:ℝ)
        · exact Cell0332.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0333.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (807/5000:ℝ)
    · by_cases h9 : a ≤ (161/1000:ℝ)
      · by_cases h10 : a ≤ (201/1250:ℝ)
        · exact Cell0334.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0335.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (403/2500:ℝ)
        · exact Cell0336.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0337.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (809/5000:ℝ)
      · by_cases h13 : a ≤ (101/625:ℝ)
        · exact Cell0338.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0339.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (81/500:ℝ)
        · exact Cell0340.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0341.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

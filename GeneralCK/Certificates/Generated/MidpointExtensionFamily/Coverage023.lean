import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0358
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0359
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0360
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0361
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0362
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0363
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0364
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0365
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0366
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0367
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0368
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0369
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0370
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0371
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0372
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0373
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage023 {a z : ℝ} (ha : Bounds (827/5000) (843/5000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (167/1000:ℝ)
  · by_cases h1 : a ≤ (831/5000:ℝ)
    · by_cases h2 : a ≤ (829/5000:ℝ)
      · by_cases h3 : a ≤ (207/1250:ℝ)
        · exact Cell0358.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0359.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (83/500:ℝ)
        · exact Cell0360.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0361.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (833/5000:ℝ)
      · by_cases h6 : a ≤ (104/625:ℝ)
        · exact Cell0362.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0363.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (417/2500:ℝ)
        · exact Cell0364.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0365.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (839/5000:ℝ)
    · by_cases h9 : a ≤ (837/5000:ℝ)
      · by_cases h10 : a ≤ (209/1250:ℝ)
        · exact Cell0366.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0367.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (419/2500:ℝ)
        · exact Cell0368.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0369.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (841/5000:ℝ)
      · by_cases h13 : a ≤ (21/125:ℝ)
        · exact Cell0370.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0371.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (421/2500:ℝ)
        · exact Cell0372.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0373.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

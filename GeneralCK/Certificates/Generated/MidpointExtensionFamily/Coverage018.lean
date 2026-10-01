import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0278
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0279
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0280
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0281
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0282
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0283
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0284
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0285
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0286
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0287
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0288
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0289
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0290
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0291
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0292
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0293
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage018 {a z : ℝ} (ha : Bounds (3/20) (763/5000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (151/1000:ℝ)
  · by_cases h1 : a ≤ (94/625:ℝ)
    · by_cases h2 : a ≤ (751/5000:ℝ)
      · by_cases h3 : a ≤ (1501/10000:ℝ)
        · exact Cell0278.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0279.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (1503/10000:ℝ)
        · exact Cell0280.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0281.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (753/5000:ℝ)
      · by_cases h6 : a ≤ (301/2000:ℝ)
        · exact Cell0282.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0283.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (377/2500:ℝ)
        · exact Cell0284.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0285.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (759/5000:ℝ)
    · by_cases h9 : a ≤ (757/5000:ℝ)
      · by_cases h10 : a ≤ (189/1250:ℝ)
        · exact Cell0286.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0287.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (379/2500:ℝ)
        · exact Cell0288.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0289.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (761/5000:ℝ)
      · by_cases h13 : a ≤ (19/125:ℝ)
        · exact Cell0290.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0291.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (381/2500:ℝ)
        · exact Cell0292.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0293.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

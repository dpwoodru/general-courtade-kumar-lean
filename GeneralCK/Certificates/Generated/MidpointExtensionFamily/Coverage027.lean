import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0422
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0423
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0424
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0425
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0426
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0427
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0428
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0429
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0430
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0431
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0432
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0433
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0434
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0435
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0436
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0437
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage027 {a z : ℝ} (ha : Bounds (19/100) (401/2000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (487/2500:ℝ)
  · by_cases h1 : a ≤ (481/2500:ℝ)
    · by_cases h2 : a ≤ (239/1250:ℝ)
      · by_cases h3 : a ≤ (953/5000:ℝ)
        · exact Cell0422.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0423.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (959/5000:ℝ)
        · exact Cell0424.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0425.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (121/625:ℝ)
      · by_cases h6 : a ≤ (193/1000:ℝ)
        · exact Cell0426.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0427.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (971/5000:ℝ)
        · exact Cell0428.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0429.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (247/1250:ℝ)
    · by_cases h9 : a ≤ (49/250:ℝ)
      · by_cases h10 : a ≤ (977/5000:ℝ)
        · exact Cell0430.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0431.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (123/625:ℝ)
        · exact Cell0432.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0433.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (249/1250:ℝ)
      · by_cases h13 : a ≤ (124/625:ℝ)
        · exact Cell0434.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0435.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (1/5:ℝ)
        · exact Cell0436.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0437.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0575
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0576
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0577
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0578
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0579
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0580
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0581
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0582
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0583
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0584
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0585
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0586
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0587
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0588
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0589
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0590
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage037 {a z : ℝ} (ha : Bounds (763/5000) (779/5000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (771/5000:ℝ)
  · by_cases h1 : a ≤ (767/5000:ℝ)
    · by_cases h2 : a ≤ (153/1000:ℝ)
      · by_cases h3 : a ≤ (191/1250:ℝ)
        · exact Cell0575.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0576.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (383/2500:ℝ)
        · exact Cell0577.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0578.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (769/5000:ℝ)
      · by_cases h6 : a ≤ (96/625:ℝ)
        · exact Cell0579.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0580.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (77/500:ℝ)
        · exact Cell0581.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0582.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (31/200:ℝ)
    · by_cases h9 : a ≤ (773/5000:ℝ)
      · by_cases h10 : a ≤ (193/1250:ℝ)
        · exact Cell0583.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0584.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (387/2500:ℝ)
        · exact Cell0585.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0586.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (777/5000:ℝ)
      · by_cases h13 : a ≤ (97/625:ℝ)
        · exact Cell0587.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0588.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (389/2500:ℝ)
        · exact Cell0589.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0590.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

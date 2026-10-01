import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0294
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0295
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0296
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0297
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0298
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0299
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0300
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0301
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0302
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0303
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0304
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0305
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0306
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0307
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0308
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0309
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage019 {a z : ℝ} (ha : Bounds (763/5000) (779/5000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (771/5000:ℝ)
  · by_cases h1 : a ≤ (767/5000:ℝ)
    · by_cases h2 : a ≤ (153/1000:ℝ)
      · by_cases h3 : a ≤ (191/1250:ℝ)
        · exact Cell0294.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0295.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (383/2500:ℝ)
        · exact Cell0296.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0297.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (769/5000:ℝ)
      · by_cases h6 : a ≤ (96/625:ℝ)
        · exact Cell0298.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0299.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (77/500:ℝ)
        · exact Cell0300.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0301.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (31/200:ℝ)
    · by_cases h9 : a ≤ (773/5000:ℝ)
      · by_cases h10 : a ≤ (193/1250:ℝ)
        · exact Cell0302.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0303.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (387/2500:ℝ)
        · exact Cell0304.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0305.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (777/5000:ℝ)
      · by_cases h13 : a ≤ (97/625:ℝ)
        · exact Cell0306.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0307.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (389/2500:ℝ)
        · exact Cell0308.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0309.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0454
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0455
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0456
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0457
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0458
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0459
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0460
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0461
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0462
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0463
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0464
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0465
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0466
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0467
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0468
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0469
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage029 {a z : ℝ} (ha : Bounds (421/2000) (453/2000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (437/2000:ℝ)
  · by_cases h1 : a ≤ (429/2000:ℝ)
    · by_cases h2 : a ≤ (17/80:ℝ)
      · by_cases h3 : a ≤ (423/2000:ℝ)
        · exact Cell0454.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0455.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (427/2000:ℝ)
        · exact Cell0456.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0457.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (433/2000:ℝ)
      · by_cases h6 : a ≤ (431/2000:ℝ)
        · exact Cell0458.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0459.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (87/400:ℝ)
        · exact Cell0460.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0461.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (89/400:ℝ)
    · by_cases h9 : a ≤ (441/2000:ℝ)
      · by_cases h10 : a ≤ (439/2000:ℝ)
        · exact Cell0462.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0463.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (443/2000:ℝ)
        · exact Cell0464.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0465.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (449/2000:ℝ)
      · by_cases h13 : a ≤ (447/2000:ℝ)
        · exact Cell0466.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0467.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (451/2000:ℝ)
        · exact Cell0468.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0469.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

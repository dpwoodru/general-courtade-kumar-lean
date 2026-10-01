import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0767
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0768
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0769
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0770
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0771
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0772
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0773
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0774
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0775
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0776
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0777
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0778
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0779
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0780
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0781
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0782
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage049 {a z : ℝ} (ha : Bounds (497/2000) (283/1000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (33/125:ℝ)
  · by_cases h1 : a ≤ (32/125:ℝ)
    · by_cases h2 : a ≤ (63/250:ℝ)
      · by_cases h3 : a ≤ (1/4:ℝ)
        · exact Cell0767.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0768.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (127/500:ℝ)
        · exact Cell0769.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0770.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (13/50:ℝ)
      · by_cases h6 : a ≤ (129/500:ℝ)
        · exact Cell0771.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0772.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (131/500:ℝ)
        · exact Cell0773.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0774.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (273/1000:ℝ)
    · by_cases h9 : a ≤ (67/250:ℝ)
      · by_cases h10 : a ≤ (133/500:ℝ)
        · exact Cell0775.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0776.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (541/2000:ℝ)
        · exact Cell0777.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0778.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (139/500:ℝ)
      · by_cases h13 : a ≤ (551/2000:ℝ)
        · exact Cell0779.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0780.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (561/2000:ℝ)
        · exact Cell0781.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0782.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

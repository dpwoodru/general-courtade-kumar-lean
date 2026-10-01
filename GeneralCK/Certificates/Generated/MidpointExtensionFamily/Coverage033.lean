import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0518
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0519
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0520
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0521
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0522
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0523
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0524
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0525
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0526
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0527
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0528
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0529
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0530
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0531
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0532
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0533
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage033 {a z : ℝ} (ha : Bounds (337/1000) (223/500) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (381/1000:ℝ)
  · by_cases h1 : a ≤ (357/1000:ℝ)
    · by_cases h2 : a ≤ (347/1000:ℝ)
      · by_cases h3 : a ≤ (171/500:ℝ)
        · exact Cell0518.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0519.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (44/125:ℝ)
        · exact Cell0520.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0521.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (369/1000:ℝ)
      · by_cases h6 : a ≤ (363/1000:ℝ)
        · exact Cell0522.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0523.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (3/8:ℝ)
        · exact Cell0524.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0525.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (41/100:ℝ)
    · by_cases h9 : a ≤ (79/200:ℝ)
      · by_cases h10 : a ≤ (97/250:ℝ)
        · exact Cell0526.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0527.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (201/500:ℝ)
        · exact Cell0528.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0529.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (427/1000:ℝ)
      · by_cases h13 : a ≤ (209/500:ℝ)
        · exact Cell0530.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0531.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (109/250:ℝ)
        · exact Cell0532.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0533.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

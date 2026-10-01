import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0390
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0391
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0392
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0393
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0394
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0395
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0396
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0397
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0398
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0399
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0400
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0401
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0402
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0403
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0404
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0405
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage025 {a z : ℝ} (ha : Bounds (7/40) (907/5000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (891/5000:ℝ)
  · by_cases h1 : a ≤ (883/5000:ℝ)
    · by_cases h2 : a ≤ (879/5000:ℝ)
      · by_cases h3 : a ≤ (877/5000:ℝ)
        · exact Cell0390.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0391.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (881/5000:ℝ)
        · exact Cell0392.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0393.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (887/5000:ℝ)
      · by_cases h6 : a ≤ (177/1000:ℝ)
        · exact Cell0394.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0395.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (889/5000:ℝ)
        · exact Cell0396.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0397.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (899/5000:ℝ)
    · by_cases h9 : a ≤ (179/1000:ℝ)
      · by_cases h10 : a ≤ (893/5000:ℝ)
        · exact Cell0398.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0399.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (897/5000:ℝ)
        · exact Cell0400.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0401.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (903/5000:ℝ)
      · by_cases h13 : a ≤ (901/5000:ℝ)
        · exact Cell0402.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0403.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (181/1000:ℝ)
        · exact Cell0404.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0405.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

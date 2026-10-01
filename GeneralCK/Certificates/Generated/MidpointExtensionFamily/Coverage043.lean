import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0671
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0672
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0673
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0674
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0675
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0676
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0677
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0678
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0679
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0680
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0681
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0682
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0683
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0684
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0685
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0686
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage043 {a z : ℝ} (ha : Bounds (7/40) (907/5000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (891/5000:ℝ)
  · by_cases h1 : a ≤ (883/5000:ℝ)
    · by_cases h2 : a ≤ (879/5000:ℝ)
      · by_cases h3 : a ≤ (877/5000:ℝ)
        · exact Cell0671.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0672.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (881/5000:ℝ)
        · exact Cell0673.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0674.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (887/5000:ℝ)
      · by_cases h6 : a ≤ (177/1000:ℝ)
        · exact Cell0675.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0676.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (889/5000:ℝ)
        · exact Cell0677.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0678.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (899/5000:ℝ)
    · by_cases h9 : a ≤ (179/1000:ℝ)
      · by_cases h10 : a ≤ (893/5000:ℝ)
        · exact Cell0679.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0680.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (897/5000:ℝ)
        · exact Cell0681.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0682.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (903/5000:ℝ)
      · by_cases h13 : a ≤ (901/5000:ℝ)
        · exact Cell0683.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0684.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (181/1000:ℝ)
        · exact Cell0685.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0686.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

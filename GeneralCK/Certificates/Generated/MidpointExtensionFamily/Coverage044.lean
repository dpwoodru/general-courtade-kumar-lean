import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0687
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0688
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0689
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0690
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0691
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0692
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0693
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0694
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0695
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0696
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0697
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0698
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0699
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0700
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0701
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0702
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage044 {a z : ℝ} (ha : Bounds (907/5000) (19/100) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (463/2500:ℝ)
  · by_cases h1 : a ≤ (183/1000:ℝ)
    · by_cases h2 : a ≤ (911/5000:ℝ)
      · by_cases h3 : a ≤ (909/5000:ℝ)
        · exact Cell0687.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0688.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (913/5000:ℝ)
        · exact Cell0689.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0690.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (23/125:ℝ)
      · by_cases h6 : a ≤ (917/5000:ℝ)
        · exact Cell0691.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0692.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (923/5000:ℝ)
        · exact Cell0693.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0694.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (469/2500:ℝ)
    · by_cases h9 : a ≤ (233/1250:ℝ)
      · by_cases h10 : a ≤ (929/5000:ℝ)
        · exact Cell0695.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0696.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (187/1000:ℝ)
        · exact Cell0697.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0698.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (118/625:ℝ)
      · by_cases h13 : a ≤ (941/5000:ℝ)
        · exact Cell0699.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0700.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (947/5000:ℝ)
        · exact Cell0701.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0702.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

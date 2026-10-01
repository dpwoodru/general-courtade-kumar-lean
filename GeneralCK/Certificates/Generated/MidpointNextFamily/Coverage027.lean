import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0432
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0433
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0434
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0435
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0436
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0437
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0438
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0439
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0440
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0441
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0442
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0443
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0444
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0445
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0446
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0447
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage027 {a z : ℝ} (ha : Bounds (291/1000) (299/1000) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(59/200:ℝ)
  · by_cases h1 : a≤(293/1000:ℝ)
    · by_cases h2 : a≤(73/250:ℝ)
      · by_cases h3 : a≤(583/2000:ℝ)
        · exact Cell0432.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0433.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(117/400:ℝ)
        · exact Cell0434.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0435.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(147/500:ℝ)
      · by_cases h6 : a≤(587/2000:ℝ)
        · exact Cell0436.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0437.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(589/2000:ℝ)
        · exact Cell0438.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0439.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(297/1000:ℝ)
    · by_cases h9 : a≤(37/125:ℝ)
      · by_cases h10 : a≤(591/2000:ℝ)
        · exact Cell0440.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0441.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(593/2000:ℝ)
        · exact Cell0442.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0443.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(149/500:ℝ)
      · by_cases h13 : a≤(119/400:ℝ)
        · exact Cell0444.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0445.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(597/2000:ℝ)
        · exact Cell0446.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0447.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

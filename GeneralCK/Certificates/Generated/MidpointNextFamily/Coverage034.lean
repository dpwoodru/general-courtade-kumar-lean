import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0544
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0545
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0546
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0547
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0548
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0549
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0550
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0551
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0552
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0553
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0554
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0555
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0556
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0557
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0558
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0559
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage034 {a z : ℝ} (ha : Bounds (197/500) (41/100) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(201/500:ℝ)
  · by_cases h1 : a≤(199/500:ℝ)
    · by_cases h2 : a≤(99/250:ℝ)
      · by_cases h3 : a≤(79/200:ℝ)
        · exact Cell0544.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0545.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(397/1000:ℝ)
        · exact Cell0546.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0547.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(2/5:ℝ)
      · by_cases h6 : a≤(399/1000:ℝ)
        · exact Cell0548.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0549.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(401/1000:ℝ)
        · exact Cell0550.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0551.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(203/500:ℝ)
    · by_cases h9 : a≤(101/250:ℝ)
      · by_cases h10 : a≤(403/1000:ℝ)
        · exact Cell0552.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0553.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(81/200:ℝ)
        · exact Cell0554.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0555.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(51/125:ℝ)
      · by_cases h13 : a≤(407/1000:ℝ)
        · exact Cell0556.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0557.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(409/1000:ℝ)
        · exact Cell0558.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0559.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

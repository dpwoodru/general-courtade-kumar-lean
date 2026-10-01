import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0176
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0177
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0178
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0179
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0180
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0181
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0182
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0183
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0184
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0185
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0186
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0187
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0188
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0189
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0190
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0191
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage011 {a z : ℝ} (ha : Bounds (463/2500) (471/2500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(467/2500:ℝ)
  · by_cases h1 : a≤(93/500:ℝ)
    · by_cases h2 : a≤(116/625:ℝ)
      · by_cases h3 : a≤(927/5000:ℝ)
        · exact Cell0176.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0177.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(929/5000:ℝ)
        · exact Cell0178.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0179.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(233/1250:ℝ)
      · by_cases h6 : a≤(931/5000:ℝ)
        · exact Cell0180.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0181.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(933/5000:ℝ)
        · exact Cell0182.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0183.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(469/2500:ℝ)
    · by_cases h9 : a≤(117/625:ℝ)
      · by_cases h10 : a≤(187/1000:ℝ)
        · exact Cell0184.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0185.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(937/5000:ℝ)
        · exact Cell0186.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0187.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(47/250:ℝ)
      · by_cases h13 : a≤(939/5000:ℝ)
        · exact Cell0188.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0189.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(941/5000:ℝ)
        · exact Cell0190.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0191.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

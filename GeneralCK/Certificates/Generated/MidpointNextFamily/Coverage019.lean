import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0304
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0305
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0306
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0307
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0308
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0309
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0310
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0311
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0312
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0313
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0314
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0315
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0316
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0317
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0318
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0319
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage019 {a z : ℝ} (ha : Bounds (227/1000) (47/200) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(231/1000:ℝ)
  · by_cases h1 : a≤(229/1000:ℝ)
    · by_cases h2 : a≤(57/250:ℝ)
      · by_cases h3 : a≤(91/400:ℝ)
        · exact Cell0304.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0305.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(457/2000:ℝ)
        · exact Cell0306.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0307.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(23/100:ℝ)
      · by_cases h6 : a≤(459/2000:ℝ)
        · exact Cell0308.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0309.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(461/2000:ℝ)
        · exact Cell0310.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0311.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(233/1000:ℝ)
    · by_cases h9 : a≤(29/125:ℝ)
      · by_cases h10 : a≤(463/2000:ℝ)
        · exact Cell0312.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0313.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(93/400:ℝ)
        · exact Cell0314.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0315.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(117/500:ℝ)
      · by_cases h13 : a≤(467/2000:ℝ)
        · exact Cell0316.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0317.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(469/2000:ℝ)
        · exact Cell0318.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0319.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

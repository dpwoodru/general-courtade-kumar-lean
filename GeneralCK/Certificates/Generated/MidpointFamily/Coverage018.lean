import GeneralCK.Certificates.Generated.MidpointFamily.Cell0288
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0289
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0290
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0291
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0292
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0293
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0294
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0295
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0296
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0297
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0298
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0299
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0300
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0301
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0302
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0303
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage018 {a z : ℝ} (ha : Bounds (219/1000) (227/1000) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(223/1000:ℝ)
  · by_cases h1 : a≤(221/1000:ℝ)
    · by_cases h2 : a≤(11/50:ℝ)
      · by_cases h3 : a≤(439/2000:ℝ)
        · exact Cell0288.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0289.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(441/2000:ℝ)
        · exact Cell0290.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0291.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(111/500:ℝ)
      · by_cases h6 : a≤(443/2000:ℝ)
        · exact Cell0292.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0293.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(89/400:ℝ)
        · exact Cell0294.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0295.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(9/40:ℝ)
    · by_cases h9 : a≤(28/125:ℝ)
      · by_cases h10 : a≤(447/2000:ℝ)
        · exact Cell0296.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0297.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(449/2000:ℝ)
        · exact Cell0298.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0299.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(113/500:ℝ)
      · by_cases h13 : a≤(451/2000:ℝ)
        · exact Cell0300.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0301.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(453/2000:ℝ)
        · exact Cell0302.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0303.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

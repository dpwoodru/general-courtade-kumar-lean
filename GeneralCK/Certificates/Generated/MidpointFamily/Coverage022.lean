import GeneralCK.Certificates.Generated.MidpointFamily.Cell0352
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0353
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0354
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0355
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0356
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0357
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0358
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0359
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0360
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0361
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0362
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0363
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0364
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0365
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0366
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0367
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage022 {a z : ℝ} (ha : Bounds (251/1000) (259/1000) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(51/200:ℝ)
  · by_cases h1 : a≤(253/1000:ℝ)
    · by_cases h2 : a≤(63/250:ℝ)
      · by_cases h3 : a≤(503/2000:ℝ)
        · exact Cell0352.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0353.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(101/400:ℝ)
        · exact Cell0354.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0355.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(127/500:ℝ)
      · by_cases h6 : a≤(507/2000:ℝ)
        · exact Cell0356.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0357.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(509/2000:ℝ)
        · exact Cell0358.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0359.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(257/1000:ℝ)
    · by_cases h9 : a≤(32/125:ℝ)
      · by_cases h10 : a≤(511/2000:ℝ)
        · exact Cell0360.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0361.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(513/2000:ℝ)
        · exact Cell0362.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0363.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(129/500:ℝ)
      · by_cases h13 : a≤(103/400:ℝ)
        · exact Cell0364.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0365.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(517/2000:ℝ)
        · exact Cell0366.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0367.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

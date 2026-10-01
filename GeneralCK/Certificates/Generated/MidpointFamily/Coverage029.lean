import GeneralCK.Certificates.Generated.MidpointFamily.Cell0464
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0465
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0466
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0467
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0468
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0469
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0470
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0471
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0472
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0473
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0474
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0475
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0476
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0477
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0478
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0479
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage029 {a z : ℝ} (ha : Bounds (157/500) (33/100) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(161/500:ℝ)
  · by_cases h1 : a≤(159/500:ℝ)
    · by_cases h2 : a≤(79/250:ℝ)
      · by_cases h3 : a≤(63/200:ℝ)
        · exact Cell0464.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0465.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(317/1000:ℝ)
        · exact Cell0466.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0467.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(8/25:ℝ)
      · by_cases h6 : a≤(319/1000:ℝ)
        · exact Cell0468.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0469.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(321/1000:ℝ)
        · exact Cell0470.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0471.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(163/500:ℝ)
    · by_cases h9 : a≤(81/250:ℝ)
      · by_cases h10 : a≤(323/1000:ℝ)
        · exact Cell0472.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0473.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(13/40:ℝ)
        · exact Cell0474.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0475.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(41/125:ℝ)
      · by_cases h13 : a≤(327/1000:ℝ)
        · exact Cell0476.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0477.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(329/1000:ℝ)
        · exact Cell0478.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0479.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0480
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0481
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0482
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0483
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0484
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0485
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0486
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0487
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0488
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0489
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0490
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0491
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0492
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0493
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0494
import GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0495
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage030 {a z : ℝ} (ha : Bounds (33/100) (173/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(169/500:ℝ)
  · by_cases h1 : a≤(167/500:ℝ)
    · by_cases h2 : a≤(83/250:ℝ)
      · by_cases h3 : a≤(331/1000:ℝ)
        · exact Cell0480.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0481.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(333/1000:ℝ)
        · exact Cell0482.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0483.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(42/125:ℝ)
      · by_cases h6 : a≤(67/200:ℝ)
        · exact Cell0484.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0485.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(337/1000:ℝ)
        · exact Cell0486.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0487.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(171/500:ℝ)
    · by_cases h9 : a≤(17/50:ℝ)
      · by_cases h10 : a≤(339/1000:ℝ)
        · exact Cell0488.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0489.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(341/1000:ℝ)
        · exact Cell0490.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0491.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(43/125:ℝ)
      · by_cases h13 : a≤(343/1000:ℝ)
        · exact Cell0492.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0493.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(69/200:ℝ)
        · exact Cell0494.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0495.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

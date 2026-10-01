import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0144
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0145
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0146
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0147
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0148
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0149
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0150
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0151
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0152
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0153
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0154
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0155
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0156
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0157
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0158
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0159
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage009 {a z : ℝ} (ha : Bounds (423/2500) (431/2500) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (427/2500:ℝ)
  · by_cases h1 : a ≤ (17/100:ℝ)
    · by_cases h2 : a ≤ (106/625:ℝ)
      · by_cases h3 : a ≤ (847/5000:ℝ)
        · exact Cell0144.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0145.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (849/5000:ℝ)
        · exact Cell0146.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0147.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (213/1250:ℝ)
      · by_cases h6 : a ≤ (851/5000:ℝ)
        · exact Cell0148.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0149.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (853/5000:ℝ)
        · exact Cell0150.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0151.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (429/2500:ℝ)
    · by_cases h9 : a ≤ (107/625:ℝ)
      · by_cases h10 : a ≤ (171/1000:ℝ)
        · exact Cell0152.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0153.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (857/5000:ℝ)
        · exact Cell0154.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0155.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (43/250:ℝ)
      · by_cases h13 : a ≤ (859/5000:ℝ)
        · exact Cell0156.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0157.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (861/5000:ℝ)
        · exact Cell0158.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0159.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

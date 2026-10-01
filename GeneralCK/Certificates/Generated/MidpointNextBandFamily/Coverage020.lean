import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0320
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0321
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0322
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0323
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0324
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0325
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0326
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0327
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0328
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0329
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0330
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0331
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0332
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0333
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0334
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0335
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage020 {a z : ℝ} (ha : Bounds (79/250) (393/1000) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (87/250:ℝ)
  · by_cases h1 : a ≤ (331/1000:ℝ)
    · by_cases h2 : a ≤ (323/1000:ℝ)
      · by_cases h3 : a ≤ (319/1000:ℝ)
        · exact Cell0320.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0321.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (327/1000:ℝ)
        · exact Cell0322.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0323.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (339/1000:ℝ)
      · by_cases h6 : a ≤ (67/200:ℝ)
        · exact Cell0324.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0325.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (343/1000:ℝ)
        · exact Cell0326.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0327.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (46/125:ℝ)
    · by_cases h9 : a ≤ (179/500:ℝ)
      · by_cases h10 : a ≤ (353/1000:ℝ)
        · exact Cell0328.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0329.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (363/1000:ℝ)
        · exact Cell0330.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0331.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (19/50:ℝ)
      · by_cases h13 : a ≤ (187/500:ℝ)
        · exact Cell0332.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0333.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (193/500:ℝ)
        · exact Cell0334.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0335.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

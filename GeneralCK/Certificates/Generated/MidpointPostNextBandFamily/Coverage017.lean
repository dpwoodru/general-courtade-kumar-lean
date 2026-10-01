import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0272
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0273
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0274
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0275
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0276
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0277
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0278
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0279
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0280
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0281
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0282
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0283
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0284
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0285
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0286
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0287
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage017 {a z : ℝ} (ha : Bounds (201/1000) (209/1000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (41/200:ℝ)
  · by_cases h1 : a ≤ (203/1000:ℝ)
    · by_cases h2 : a ≤ (101/500:ℝ)
      · by_cases h3 : a ≤ (403/2000:ℝ)
        · exact Cell0272.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0273.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (81/400:ℝ)
        · exact Cell0274.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0275.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (51/250:ℝ)
      · by_cases h6 : a ≤ (407/2000:ℝ)
        · exact Cell0276.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0277.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (409/2000:ℝ)
        · exact Cell0278.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0279.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (207/1000:ℝ)
    · by_cases h9 : a ≤ (103/500:ℝ)
      · by_cases h10 : a ≤ (411/2000:ℝ)
        · exact Cell0280.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0281.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (413/2000:ℝ)
        · exact Cell0282.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0283.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (26/125:ℝ)
      · by_cases h13 : a ≤ (83/400:ℝ)
        · exact Cell0284.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0285.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (417/2000:ℝ)
        · exact Cell0286.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0287.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

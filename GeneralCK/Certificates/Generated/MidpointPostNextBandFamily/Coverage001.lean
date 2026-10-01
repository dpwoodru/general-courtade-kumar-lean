import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0016
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0017
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0018
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0019
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0020
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0021
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0022
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0023
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0024
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0025
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0026
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0027
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0028
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0029
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0030
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0031
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage001 {a z : ℝ} (ha : Bounds (377/2500) (379/2500) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (189/1250:ℝ)
  · by_cases h1 : a ≤ (151/1000:ℝ)
    · by_cases h2 : a ≤ (1509/10000:ℝ)
      · by_cases h3 : a ≤ (3017/20000:ℝ)
        · exact Cell0016.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0017.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (3019/20000:ℝ)
        · exact Cell0018.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0019.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (1511/10000:ℝ)
      · by_cases h6 : a ≤ (3021/20000:ℝ)
        · exact Cell0020.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0021.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (3023/20000:ℝ)
        · exact Cell0022.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0023.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (757/5000:ℝ)
    · by_cases h9 : a ≤ (1513/10000:ℝ)
      · by_cases h10 : a ≤ (121/800:ℝ)
        · exact Cell0024.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0025.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (3027/20000:ℝ)
        · exact Cell0026.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0027.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (303/2000:ℝ)
      · by_cases h13 : a ≤ (3029/20000:ℝ)
        · exact Cell0028.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0029.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (3031/20000:ℝ)
        · exact Cell0030.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0031.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

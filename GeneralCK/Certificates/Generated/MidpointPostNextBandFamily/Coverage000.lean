import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0000
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0001
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0002
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0003
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0004
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0005
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0006
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0007
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0008
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0009
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0010
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0011
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0012
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0013
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0014
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0015
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage000 {a z : ℝ} (ha : Bounds (3/20) (377/2500) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (94/625:ℝ)
  · by_cases h1 : a ≤ (751/5000:ℝ)
    · by_cases h2 : a ≤ (1501/10000:ℝ)
      · by_cases h3 : a ≤ (3001/20000:ℝ)
        · exact Cell0000.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0001.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (3003/20000:ℝ)
        · exact Cell0002.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0003.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (1503/10000:ℝ)
      · by_cases h6 : a ≤ (601/4000:ℝ)
        · exact Cell0004.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0005.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (3007/20000:ℝ)
        · exact Cell0006.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0007.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (753/5000:ℝ)
    · by_cases h9 : a ≤ (301/2000:ℝ)
      · by_cases h10 : a ≤ (3009/20000:ℝ)
        · exact Cell0008.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0009.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (3011/20000:ℝ)
        · exact Cell0010.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0011.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (1507/10000:ℝ)
      · by_cases h13 : a ≤ (3013/20000:ℝ)
        · exact Cell0012.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0013.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (603/4000:ℝ)
        · exact Cell0014.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0015.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

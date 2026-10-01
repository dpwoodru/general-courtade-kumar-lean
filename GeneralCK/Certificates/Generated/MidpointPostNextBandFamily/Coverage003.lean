import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0048
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0049
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0050
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0051
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0052
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0053
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0054
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0055
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0056
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0057
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0058
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0059
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0060
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0061
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0062
import GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0063
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage003 {a z : ℝ} (ha : Bounds (1531/10000) (1547/10000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (1539/10000:ℝ)
  · by_cases h1 : a ≤ (307/2000:ℝ)
    · by_cases h2 : a ≤ (1533/10000:ℝ)
      · by_cases h3 : a ≤ (383/2500:ℝ)
        · exact Cell0048.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0049.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (767/5000:ℝ)
        · exact Cell0050.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0051.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (1537/10000:ℝ)
      · by_cases h6 : a ≤ (96/625:ℝ)
        · exact Cell0052.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0053.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (769/5000:ℝ)
        · exact Cell0054.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0055.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (1543/10000:ℝ)
    · by_cases h9 : a ≤ (1541/10000:ℝ)
      · by_cases h10 : a ≤ (77/500:ℝ)
        · exact Cell0056.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0057.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (771/5000:ℝ)
        · exact Cell0058.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0059.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (309/2000:ℝ)
      · by_cases h13 : a ≤ (193/1250:ℝ)
        · exact Cell0060.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0061.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (773/5000:ℝ)
        · exact Cell0062.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0063.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

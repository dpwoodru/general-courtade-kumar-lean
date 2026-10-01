import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0032
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0033
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0034
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0035
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0036
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0037
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0038
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0039
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0040
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0041
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0042
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0043
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0044
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0045
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0046
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0047
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage002 {a z : ℝ} (ha : Bounds (383/2500) (387/2500) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (77/500:ℝ)
  · by_cases h1 : a ≤ (96/625:ℝ)
    · by_cases h2 : a ≤ (767/5000:ℝ)
      · by_cases h3 : a ≤ (1533/10000:ℝ)
        · exact Cell0032.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0033.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (307/2000:ℝ)
        · exact Cell0034.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0035.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (769/5000:ℝ)
      · by_cases h6 : a ≤ (1537/10000:ℝ)
        · exact Cell0036.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0037.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (1539/10000:ℝ)
        · exact Cell0038.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0039.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (193/1250:ℝ)
    · by_cases h9 : a ≤ (771/5000:ℝ)
      · by_cases h10 : a ≤ (1541/10000:ℝ)
        · exact Cell0040.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0041.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (1543/10000:ℝ)
        · exact Cell0042.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0043.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (773/5000:ℝ)
      · by_cases h13 : a ≤ (309/2000:ℝ)
        · exact Cell0044.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0045.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (1547/10000:ℝ)
        · exact Cell0046.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0047.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

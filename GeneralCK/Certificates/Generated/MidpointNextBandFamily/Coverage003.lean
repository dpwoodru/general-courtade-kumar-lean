import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0048
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0049
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0050
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0051
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0052
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0053
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0054
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0055
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0056
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0057
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0058
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0059
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0060
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0061
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0062
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0063
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage003 {a z : ℝ} (ha : Bounds (387/2500) (391/2500) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (389/2500:ℝ)
  · by_cases h1 : a ≤ (97/625:ℝ)
    · by_cases h2 : a ≤ (31/200:ℝ)
      · by_cases h3 : a ≤ (1549/10000:ℝ)
        · exact Cell0048.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0049.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (1551/10000:ℝ)
        · exact Cell0050.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0051.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (777/5000:ℝ)
      · by_cases h6 : a ≤ (1553/10000:ℝ)
        · exact Cell0052.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0053.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (311/2000:ℝ)
        · exact Cell0054.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0055.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (39/250:ℝ)
    · by_cases h9 : a ≤ (779/5000:ℝ)
      · by_cases h10 : a ≤ (1557/10000:ℝ)
        · exact Cell0056.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0057.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (1559/10000:ℝ)
        · exact Cell0058.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0059.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (781/5000:ℝ)
      · by_cases h13 : a ≤ (1561/10000:ℝ)
        · exact Cell0060.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0061.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (1563/10000:ℝ)
        · exact Cell0062.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0063.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

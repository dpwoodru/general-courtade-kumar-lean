import GeneralCK.Certificates.Generated.MidpointFamily.Cell0448
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0449
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0450
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0451
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0452
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0453
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0454
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0455
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0456
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0457
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0458
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0459
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0460
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0461
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0462
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0463
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage028 {a z : ℝ} (ha : Bounds (299/1000) (157/500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(153/500:ℝ)
  · by_cases h1 : a≤(151/500:ℝ)
    · by_cases h2 : a≤(3/10:ℝ)
      · by_cases h3 : a≤(599/2000:ℝ)
        · exact Cell0448.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0449.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(301/1000:ℝ)
        · exact Cell0450.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0451.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(38/125:ℝ)
      · by_cases h6 : a≤(303/1000:ℝ)
        · exact Cell0452.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0453.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(61/200:ℝ)
        · exact Cell0454.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0455.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(31/100:ℝ)
    · by_cases h9 : a≤(77/250:ℝ)
      · by_cases h10 : a≤(307/1000:ℝ)
        · exact Cell0456.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0457.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(309/1000:ℝ)
        · exact Cell0458.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0459.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(39/125:ℝ)
      · by_cases h13 : a≤(311/1000:ℝ)
        · exact Cell0460.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0461.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(313/1000:ℝ)
        · exact Cell0462.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0463.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

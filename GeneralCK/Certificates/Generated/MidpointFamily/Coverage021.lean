import GeneralCK.Certificates.Generated.MidpointFamily.Cell0336
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0337
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0338
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0339
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0340
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0341
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0342
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0343
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0344
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0345
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0346
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0347
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0348
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0349
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0350
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0351
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage021 {a z : ℝ} (ha : Bounds (243/1000) (251/1000) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(247/1000:ℝ)
  · by_cases h1 : a≤(49/200:ℝ)
    · by_cases h2 : a≤(61/250:ℝ)
      · by_cases h3 : a≤(487/2000:ℝ)
        · exact Cell0336.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0337.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(489/2000:ℝ)
        · exact Cell0338.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0339.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(123/500:ℝ)
      · by_cases h6 : a≤(491/2000:ℝ)
        · exact Cell0340.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0341.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(493/2000:ℝ)
        · exact Cell0342.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0343.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(249/1000:ℝ)
    · by_cases h9 : a≤(31/125:ℝ)
      · by_cases h10 : a≤(99/400:ℝ)
        · exact Cell0344.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0345.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(497/2000:ℝ)
        · exact Cell0346.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0347.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(1/4:ℝ)
      · by_cases h13 : a≤(499/2000:ℝ)
        · exact Cell0348.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0349.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(501/2000:ℝ)
        · exact Cell0350.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0351.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

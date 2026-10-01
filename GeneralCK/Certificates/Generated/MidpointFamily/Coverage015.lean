import GeneralCK.Certificates.Generated.MidpointFamily.Cell0240
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0241
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0242
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0243
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0244
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0245
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0246
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0247
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0248
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0249
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0250
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0251
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0252
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0253
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0254
import GeneralCK.Certificates.Generated.MidpointFamily.Cell0255
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage015 {a z : ℝ} (ha : Bounds (99/500) (203/1000) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(499/2500:ℝ)
  · by_cases h1 : a≤(497/2500:ℝ)
    · by_cases h2 : a≤(124/625:ℝ)
      · by_cases h3 : a≤(991/5000:ℝ)
        · exact Cell0240.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0241.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(993/5000:ℝ)
        · exact Cell0242.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0243.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(249/1250:ℝ)
      · by_cases h6 : a≤(199/1000:ℝ)
        · exact Cell0244.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0245.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(997/5000:ℝ)
        · exact Cell0246.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0247.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(201/1000:ℝ)
    · by_cases h9 : a≤(1/5:ℝ)
      · by_cases h10 : a≤(999/5000:ℝ)
        · exact Cell0248.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0249.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(401/2000:ℝ)
        · exact Cell0250.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0251.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(101/500:ℝ)
      · by_cases h13 : a≤(403/2000:ℝ)
        · exact Cell0252.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0253.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(81/400:ℝ)
        · exact Cell0254.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0255.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

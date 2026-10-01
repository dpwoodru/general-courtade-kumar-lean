import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0374
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0375
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0376
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0377
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0378
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0379
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0380
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0381
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0382
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0383
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0384
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0385
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0386
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0387
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0388
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Cell0389
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage024 {a z : ℝ} (ha : Bounds (843/5000) (7/40) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (859/5000:ℝ)
  · by_cases h1 : a ≤ (851/5000:ℝ)
    · by_cases h2 : a ≤ (847/5000:ℝ)
      · by_cases h3 : a ≤ (169/1000:ℝ)
        · exact Cell0374.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0375.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (849/5000:ℝ)
        · exact Cell0376.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0377.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (171/1000:ℝ)
      · by_cases h6 : a ≤ (853/5000:ℝ)
        · exact Cell0378.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0379.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (857/5000:ℝ)
        · exact Cell0380.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0381.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (867/5000:ℝ)
    · by_cases h9 : a ≤ (863/5000:ℝ)
      · by_cases h10 : a ≤ (861/5000:ℝ)
        · exact Cell0382.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0383.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (173/1000:ℝ)
        · exact Cell0384.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0385.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (871/5000:ℝ)
      · by_cases h13 : a ≤ (869/5000:ℝ)
        · exact Cell0386.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0387.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (873/5000:ℝ)
        · exact Cell0388.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0389.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage036
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage037
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage038
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage039
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage040
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage041
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage042
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage043
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage044
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage045
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage046
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage047
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage048
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage049
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage050
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage051
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage052
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage053
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem bandcertificate002 {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (19/100:ℝ)
  · by_cases h1 : a ≤ (811/5000:ℝ)
    · by_cases h2 : a ≤ (779/5000:ℝ)
      · by_cases h3 : a ≤ (763/5000:ℝ)
        · exact coverage036 ⟨ha.1,h3⟩ hz
        · exact coverage037 ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (159/1000:ℝ)
        · exact coverage038 ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact coverage039 ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (843/5000:ℝ)
      · by_cases h6 : a ≤ (827/5000:ℝ)
        · exact coverage040 ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact coverage041 ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (7/40:ℝ)
        · exact coverage042 ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · by_cases h8 : a ≤ (907/5000:ℝ)
          · exact coverage043 ⟨(le_of_lt (lt_of_not_ge h7)),h8⟩ hz
          · exact coverage044 ⟨(le_of_lt (lt_of_not_ge h8)),h0⟩ hz
  · by_cases h9 : a ≤ (497/2000:ℝ)
    · by_cases h10 : a ≤ (421/2000:ℝ)
      · by_cases h11 : a ≤ (401/2000:ℝ)
        · exact coverage045 ⟨(le_of_lt (lt_of_not_ge h0)),h11⟩ hz
        · exact coverage046 ⟨(le_of_lt (lt_of_not_ge h11)),h10⟩ hz
      · by_cases h12 : a ≤ (453/2000:ℝ)
        · exact coverage047 ⟨(le_of_lt (lt_of_not_ge h10)),h12⟩ hz
        · exact coverage048 ⟨(le_of_lt (lt_of_not_ge h12)),h9⟩ hz
    · by_cases h13 : a ≤ (337/1000:ℝ)
      · by_cases h14 : a ≤ (283/1000:ℝ)
        · exact coverage049 ⟨(le_of_lt (lt_of_not_ge h9)),h14⟩ hz
        · exact coverage050 ⟨(le_of_lt (lt_of_not_ge h14)),h13⟩ hz
      · by_cases h15 : a ≤ (223/500:ℝ)
        · exact coverage051 ⟨(le_of_lt (lt_of_not_ge h13)),h15⟩ hz
        · by_cases h16 : a ≤ (361/500:ℝ)
          · exact coverage052 ⟨(le_of_lt (lt_of_not_ge h15)),h16⟩ hz
          · exact coverage053 ⟨(le_of_lt (lt_of_not_ge h16)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

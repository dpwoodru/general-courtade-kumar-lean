import GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate000
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate001
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.BandCertificate002
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem full_midpoint_extension {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (1/20) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : z ≤ (81/1000:ℝ)
  · exact bandcertificate000 ha ⟨hz.1,h0⟩
  · by_cases h1 : z ≤ (2033/25000:ℝ)
    · exact bandcertificate001 ha ⟨le_of_lt (lt_of_not_ge h0),h1⟩
    · exact bandcertificate002 ha ⟨le_of_lt (lt_of_not_ge h1),hz.2⟩
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

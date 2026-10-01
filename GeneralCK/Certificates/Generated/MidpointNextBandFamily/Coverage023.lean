import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0368
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage023 {a z : ℝ} (ha : Bounds (499/500) (999/1000) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  exact Cell0368.curvature_pos ⟨ha.1,ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

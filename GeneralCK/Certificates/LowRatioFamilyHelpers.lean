import GeneralCK.ReflectionSmallRatioFormula

namespace GeneralCK.Certificates.LowRatioFamily

theorem base_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    2*a/(1-a^2)^2 ≤ 2*b/(1-b^2)^2 := by
  have hb0 : 0 < b := ha.trans_le hab
  have hd : 0 < 1-b^2 := by nlinarith
  have hs : a^2 ≤ b^2 := (sq_le_sq₀ ha.le hb0.le).mpr hab
  have hda : 0 < 1-a^2 := by linarith
  have hsq : (1-b^2)^2 ≤ (1-a^2)^2 := (sq_le_sq₀ hd.le hda.le).mpr (by linarith)
  exact div_le_div₀ (by positivity) (by nlinarith) (sq_pos_of_pos hd) hsq

end GeneralCK.Certificates.LowRatioFamily

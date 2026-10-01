import GeneralCK.PureGapZeroCapLeftUpperHalfCollarQuartic

/-!
Conditional transfer from a uniform C=600 estimate of the *actual radial
expression* to the strict left-upper half-collar canonical gap. The
radial estimate remains an explicit premise.
-/

namespace GeneralCK

theorem leftUpper_halfCollar_nonneg_of_radial_C600
    {z lambda : ℝ}
    (hz : 0 < z) (hzmax : z ≤ 1 / 64)
    (hlambda : 0 < lambda) (hlambda1 : lambda < 1)
    (habs :
      |(interiorCost (1 / 2 - z) (1 / 2 - lambda * z) +
          2 * F (1 / 2 - (1 / 2 - z))
            ((H (1 / 2 - z) + H (1 / 2 - lambda * z)) / 2) -
          F ((1 / 2 - lambda * z) - (1 / 2 - z))
            ((H (1 / 2 - z) + H (1 / 2 - lambda * z)) / 2) -
          eta ((H (1 / 2 - z) + H (1 / 2 - lambda * z)) / 2) +
          eta (H (1 / 2 - lambda * z)) / 2) -
        z ^ 4 * leftUpperQuarticCoefficient (Real.log 2) lambda| ≤
      600 * z ^ 6) :
    0 ≤ canonicalPureGap (1 / 2 - z) (1 / 2)
      (H (1 / 2 - z)) (H (1 / 2 - lambda * z)) := by
  have ha : 0 < 1 / 2 - z := by linarith
  have hab : 1 / 2 - z < 1 / 2 - lambda * z := by
    nlinarith [mul_lt_mul_of_pos_right hlambda1 hz]
  have hb : 1 / 2 - lambda * z < 1 / 2 := by
    nlinarith [mul_pos hlambda hz]
  have hRad := canonicalPureGap_leftUpper_radial_eq ha hab hb
  have hlow := (abs_le.mp habs).1
  apply leftUpper_halfCollar_nonneg_of_remainder
    hz hzmax (by norm_num) (by norm_num : (600 : ℝ) * (1 / 64) ^ 2 ≤ 35 / 48)
  rw [hRad]
  linarith

#print axioms leftUpper_halfCollar_nonneg_of_radial_C600

end GeneralCK

import GeneralCK.PureGapE8AnalyticRealBridge

/-!
# Stable exponential coordinates for the E8 positive-axis inverse

These are the scalar functions used by the historical `xy_jets5` program.
The identities below identify its positive-parameter values with the existing
real analytic parametrization, and therefore with the concrete inverse `e8Q`.
-/

namespace GeneralCK.Certificates.E8TAxisStableScalar

open GeneralCK.Reflection GeneralCK.Certificates.Reflection
open GeneralCK.E8AnalyticGerm

noncomputable def z (a : ℝ) : ℝ := Real.exp (-2 * a)
noncomputable def r (a : ℝ) : ℝ := (1 - z a) / (1 + z a)
noncomputable def q (a : ℝ) : ℝ := 4 * z a / (1 + z a) ^ 2
noncomputable def l1 (a : ℝ) : ℝ := Real.log (1 + z a)
noncomputable def ell (a : ℝ) : ℝ := a + l1 a
noncomputable def h (a : ℝ) : ℝ := l1 a + 2 * a * z a / (1 + z a)
noncomputable def X (a : ℝ) : ℝ := Real.log 2 * r a / (2 * h a)
noncomputable def Y (a : ℝ) : ℝ :=
  (2 / Real.log 2) * (a + r a * h a / (q a * ell a))

theorem z_pos (a : ℝ) : 0 < z a := Real.exp_pos _

theorem one_add_z_pos (a : ℝ) : 0 < 1 + z a := by
  linarith [z_pos a]

theorem z_lt_one {a : ℝ} (ha : 0 < a) : z a < 1 := by
  exact Real.exp_lt_one_iff.mpr (by linarith)

theorem r_pos {a : ℝ} (ha : 0 < a) : 0 < r a := by
  exact div_pos (sub_pos.mpr (z_lt_one ha)) (one_add_z_pos a)

theorem r_lt_one (a : ℝ) : r a < 1 := by
  change (1 - z a) / (1 + z a) < 1
  apply (div_lt_one (one_add_z_pos a)).mpr
  linarith [z_pos a]

theorem one_add_r (a : ℝ) : 1 + r a = 2 / (1 + z a) := by
  unfold r
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem one_sub_r (a : ℝ) : 1 - r a = 2 * z a / (1 + z a) := by
  unfold r
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem one_add_r_pos (a : ℝ) : 0 < 1 + r a := by
  rw [one_add_r]
  exact div_pos (by norm_num) (one_add_z_pos a)

theorem one_sub_r_pos (a : ℝ) : 0 < 1 - r a := by
  linarith [r_lt_one a]

theorem q_pos (a : ℝ) : 0 < q a := by
  unfold q
  exact div_pos (mul_pos (by norm_num) (z_pos a)) (pow_pos (one_add_z_pos a) 2)

theorem one_sub_r_sq (a : ℝ) : 1 - r a ^ 2 = q a := by
  unfold r q
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem log_one_add_r (a : ℝ) :
    Real.log (1 + r a) = Real.log 2 - l1 a := by
  rw [one_add_r]
  exact Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (one_add_z_pos a).ne'

theorem log_one_sub_r (a : ℝ) :
    Real.log (1 - r a) = Real.log 2 - 2 * a - l1 a := by
  rw [one_sub_r, Real.log_div (mul_ne_zero (by norm_num) (z_pos a).ne')
      (one_add_z_pos a).ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (z_pos a).ne']
  simp only [z, Real.log_exp, l1]
  ring

theorem A_r (a : ℝ) : SmallMean.A (r a) = a := by
  unfold SmallMean.A
  rw [Real.log_div (one_add_r_pos a).ne' (one_sub_r_pos a).ne',
    log_one_add_r, log_one_sub_r]
  ring

theorem biasB_r (a : ℝ) : biasB (r a) = ell a := by
  unfold biasB
  rw [show 1 - r a * r a = (1 + r a) * (1 - r a) by ring,
    Real.log_mul (one_add_r_pos a).ne' (one_sub_r_pos a).ne',
    log_one_add_r, log_one_sub_r]
  unfold ell
  ring

theorem biasE_r (a : ℝ) : biasE (r a) = h a := by
  unfold biasE
  rw [log_one_add_r, log_one_sub_r, one_add_r, one_sub_r]
  unfold h
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem ell_pos {a : ℝ} (ha : 0 < a) : 0 < ell a := by
  rw [← biasB_r]
  exact biasB_pos (r_pos ha) (r_lt_one a)

theorem h_pos {a : ℝ} (ha : 0 < a) : 0 < h a := by
  rw [← biasE_r]
  exact biasE_pos_wide (by linarith [r_pos ha]) (r_lt_one a)

theorem X_eq_xParamReal (a : ℝ) : X a = xParamReal (r a) := by
  unfold X xParamReal
  rw [biasE_r]

theorem Y_eq_thetaParamReal (a : ℝ) : Y a = thetaParamReal (r a) := by
  unfold Y thetaParamReal
  rw [A_r, biasE_r, one_sub_r_sq, biasB_r]

theorem X_pos {a : ℝ} (ha : 0 < a) : 0 < X a := by
  unfold X
  exact div_pos (mul_pos (Real.log_pos (by norm_num)) (r_pos ha))
    (mul_pos (by norm_num) (h_pos ha))

theorem Y_pos {a : ℝ} (ha : 0 < a) : 0 < Y a := by
  unfold Y
  exact mul_pos (div_pos (by norm_num) (Real.log_pos (by norm_num)))
    (add_pos ha (div_pos (mul_pos (r_pos ha) (h_pos ha))
      (mul_pos (q_pos a) (ell_pos ha))))

theorem e8Theta_X {a : ℝ} (ha : 0 < a) : e8Theta (X a) = Y a := by
  rw [X_eq_xParamReal, Y_eq_thetaParamReal]
  exact e8Theta_xParamReal (r_pos ha) (r_lt_one a)

theorem e8Q_Y {a : ℝ} (ha : 0 < a) : e8Q (Y a) = X a := by
  rw [X_eq_xParamReal, Y_eq_thetaParamReal]
  exact e8Q_thetaParamReal (r_pos ha) (r_lt_one a)

end GeneralCK.Certificates.E8TAxisStableScalar

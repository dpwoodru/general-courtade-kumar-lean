import GeneralCK.SmallMeanEstimates

namespace GeneralCK
open Set
open SmallMean

theorem Cn_ratio_strictMonoOn : StrictMonoOn (fun r => Cn r/r^2) (Ioc (0:ℝ) 1) := by
  have hd : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt (fun r => Cn r/r^2)
      ((r*A r-2*Cn r)/r^3) r := by
    intro r hr
    have h := (hasDerivAt_Cn (by linarith [hr.1]) hr.2).div
      ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr.1.ne')
    convert! h using 1
    simp only [Pi.pow_apply,id_eq]
    field_simp [hr.1.ne']
    ring
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioc 0 1)
  · intro r hr
    exact (Cn_continuous.continuousAt.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hr.1.ne')).continuousWithinAt
  · intro r hr
    exact (hd r (by simpa only [interior_Ioc] using hr)).hasDerivWithinAt
  · intro r hr
    rw [interior_Ioc] at hr
    have hc := Cn_pos hr.1 hr.2.le
    have hb := mean_cost_bonus hr.1.le hr.2
    have hp : 0 < r^2*Cn r := mul_pos (sq_pos_of_pos hr.1) hc
    exact div_pos (by nlinarith) (pow_pos hr.1 3)

theorem Cn_lt_log_two_mul_sq {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    Cn r < Real.log 2*r^2 := by
  have h := Cn_ratio_strictMonoOn ⟨hr,hr'.le⟩ (by norm_num : (1:ℝ) ∈ Ioc 0 1) hr'
  dsimp only at h
  rw [Cn_one,one_pow,div_one] at h
  exact (div_lt_iff₀ (sq_pos_of_pos hr)).mp h

theorem H_gt_parabola {p : ℝ} (hp : 0 < p) (hp' : p < 1/2) :
    4*p*(1-p) < H p := by
  have hc := Cn_lt_log_two_mul_sq (r := 1-2*p) (by linarith) (by linarith)
  unfold Cn at hc
  rw [show (1-(1-2*p))/2=p by ring] at hc
  have hl := (mul_lt_mul_iff_right₀ log_two_pos).mp hc
  nlinarith

end GeneralCK

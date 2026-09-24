import GeneralCK.SmallBoundaryPhiLowContactTail

namespace GeneralCK.SmallBoundaryPhiSchur

open Set

set_option maxHeartbeats 800000

noncomputable def tailZ (t : ℝ) : ℝ := 1/(-Real.log t)
noncomputable def tailB (t : ℝ) : ℝ := -Real.log (1-t)/t

theorem tailZ_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : 0 < tailZ t :=
  div_pos one_pos (neg_pos.mpr (Real.log_neg ht ht1))

theorem tailB_bounds {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    1 ≤ tailB t ∧ tailB t ≤ 1/(1-t) := by
  have hc : 0 < 1-t := by linarith
  have hlo : t ≤ -Real.log (1-t) := by linarith [Real.log_le_sub_one_of_pos hc]
  have hhi := Real.log_le_sub_one_of_pos (inv_pos.mpr hc)
  rw [Real.log_inv] at hhi
  constructor
  · apply (le_div_iff₀ ht).mpr
    simpa using hlo
  · apply (div_le_iff₀ ht).mpr
    calc
      -Real.log (1-t) ≤ (1-t)⁻¹-1 := hhi
      _ = 1/(1-t)*t := by field_simp; ring

/-- The rational contact floor puts every doubled-tail contact in the
closed certificate box without evaluating an exponential. -/
theorem tail_coordinates_box {t : ℝ} (ht : 0 < t) (htu : t ≤ 2*tailDelta) :
    t ≤ 1/10000 ∧ 0 < tailZ t ∧ tailZ t ≤ 1/49 ∧
    0 ≤ tailB t-1 ∧ tailB t-1 ≤ 1/10000 := by
  have ht1 : t < 1 := by dsimp [tailDelta] at htu; linarith
  have hc : 0 < 1-t := by linarith
  have hi : (2:ℝ)^72 ≤ t⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ ht).mpr
    exact (mul_le_mul_of_nonneg_left htu (by positivity)).trans (by norm_num [tailDelta])
  have hl := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^72) hi
  rw [Real.log_pow, Real.log_inv] at hl
  norm_num at hl
  have hL : (69/100:ℝ) ≤ Real.log 2 := by
    have hs := Certificates.PilotData.log_two.1
    norm_num at hs
    linarith
  have hx : 49 ≤ -Real.log t := by linarith
  have hz := tailZ_pos ht ht1
  have hzU : tailZ t ≤ 1/49 := by
    exact one_div_le_one_div_of_le (by norm_num) hx
  have hb := tailB_bounds ht ht1
  have hbU : 1/(1-t) ≤ 10001/10000 := by
    apply (div_le_iff₀ hc).mpr
    dsimp [tailDelta] at htu
    linarith
  refine ⟨?_,hz,hzU,by linarith [hb.1],by linarith [hb.2]⟩
  dsimp [tailDelta] at htu
  linarith

theorem log_eq_tailZ {t : ℝ} (_ht : 0 < t) (_ht1 : t < 1) :
    Real.log t = -1/tailZ t := by
  dsimp [tailZ]
  field_simp

theorem log_complement_eq_tailB (t : ℝ) (ht : t ≠ 0) :
    Real.log (1-t) = -t*tailB t := by
  dsimp [tailB]
  field_simp

theorem hasDerivAt_tailZ {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt tailZ ((tailZ t)^2/t) t := by
  have hn : -Real.log t ≠ 0 := ne_of_gt (neg_pos.mpr (Real.log_neg ht ht1))
  have hd := (hasDerivAt_const t (1:ℝ)).div (Real.hasDerivAt_log ht.ne').neg hn
  convert! hd using 1
  dsimp [tailZ]
  field_simp
  ring

theorem hasDerivAt_tailB {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt tailB ((1/(1-t)-tailB t)/t) t := by
  have hc : 1-t ≠ 0 := by linarith
  have hd := ((((hasDerivAt_id t).const_sub 1).log hc).neg).div (hasDerivAt_id t) ht.ne'
  convert! hd using 1
  dsimp [tailB]
  field_simp

theorem hn_eq_tailCoordinates {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Certificates.Mixed.hn t =
      (t/tailZ t)*(1+(1-t)*tailB t*tailZ t) := by
  unfold Certificates.Mixed.hn
  rw [log_eq_tailZ ht ht1, log_complement_eq_tailB t ht.ne']
  field_simp [(tailZ_pos ht ht1).ne']
  ring

#print axioms tailB_bounds
#print axioms tail_coordinates_box
#print axioms hasDerivAt_tailZ
#print axioms hasDerivAt_tailB
#print axioms hn_eq_tailCoordinates

end GeneralCK.SmallBoundaryPhiSchur

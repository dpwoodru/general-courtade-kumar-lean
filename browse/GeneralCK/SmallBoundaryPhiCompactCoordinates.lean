import GeneralCK.SmallBoundaryPhiCompactTransport
import GeneralCK.SmallBoundaryPhiTailCoordinates

/-! Inclusive logarithmic-coordinate bounds on the compact owner's interval. -/

namespace GeneralCK.SmallBoundaryPhiSchur

open SmallMeanPhiCutoff

theorem compactDelta_pos : 0 < compactDelta := by norm_num [compactDelta]

theorem compactDelta_le_retainedCutoff : compactDelta ≤ retainedCutoff := by
  norm_num [compactDelta, retainedCutoff]

theorem compact_coordinates_box {t : ℝ} (ht : 0 < t) (htu : t ≤ retainedCutoff) :
    t ≤ 1/10000 ∧ 0 < tailZ t ∧ tailZ t ≤ 1/9 ∧
    0 ≤ tailB t-1 ∧ tailB t-1 ≤ 1/9999 := by
  have ht1 : t < 1 := by dsimp [retainedCutoff] at htu; linarith
  have hc : 0 < 1-t := by linarith
  have hi : (2:ℝ)^13 ≤ t⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ ht).mpr
    exact (mul_le_mul_of_nonneg_left htu (by positivity)).trans (by norm_num [retainedCutoff])
  have hl := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^13) hi
  rw [Real.log_pow, Real.log_inv] at hl
  norm_num at hl
  have hL : (693/1000:ℝ) ≤ Real.log 2 := by
    have hs := Certificates.PilotData.log_two.1
    norm_num at hs
    linarith
  have hx : 9 ≤ -Real.log t := by linarith
  have hz := tailZ_pos ht ht1
  have hzU : tailZ t ≤ 1/9 := one_div_le_one_div_of_le (by norm_num) hx
  have hb := tailB_bounds ht ht1
  have hbU : 1/(1-t) ≤ 10000/9999 := by
    apply (div_le_iff₀ hc).mpr
    dsimp [retainedCutoff] at htu
    linarith
  exact ⟨htu,hz,hzU,by linarith [hb.1],by linarith [hb.2]⟩

#print axioms compactDelta_pos
#print axioms compactDelta_le_retainedCutoff
#print axioms compact_coordinates_box

end GeneralCK.SmallBoundaryPhiSchur

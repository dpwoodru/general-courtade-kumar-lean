import GeneralCK.Certificates.SmallMeanLeaves
import GeneralCK.Certificates.SmallMeanSlopeBounds

namespace GeneralCK.Certificates.SmallMean

theorem fixed_inverse_bracket :
    (16282259 / 67108864) ≤ entropyInverse (1-H (1/32)) ∧
    entropyInverse (1-H (1/32)) ≤ (4070565 / 16777216) := by
  have ht := entropy_1
  have hl := entropy_6
  have hu := entropy_7
  exact inverse_bracket (by linarith) (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith only [ht.2, hl.2]) (by linarith only [ht.1, hu.1])

theorem fixed_logit_lower : (17786621 / 15625000) ≤ Real.log ((1-(4070565 / 16777216))/(4070565 / 16777216)) := by
  have hv := log_v_7.1
  have hc := log_c_7.2
  rw [Real.log_div (by norm_num) (by norm_num)]
  norm_num
  linarith only [hv, hc]

theorem fixed_secant_lt :
    (deriv Scalar.P (H (1/32))-4)/H (1/32) < (23/10 : ℝ) := by
  have ht := entropy_1
  have ht0 : 0 < H (1/32) := by linarith only [ht.1]
  have ht1 : H (1/32) < 1 := by linarith only [ht.2]
  have hb := slope_upper ht0 ht1 (l := (16282259 / 67108864)) (u := (4070565 / 16777216))
    (j := (17786621 / 15625000)) (by norm_num) (by norm_num)
    fixed_inverse_bracket.1 fixed_inverse_bracket.2 fixed_logit_lower (by norm_num)
  have hn : 2+(1-2*((16282259 / 67108864) : ℝ))/((16282259 / 67108864)*(1-(4070565 / 16777216))*(17786621 / 15625000))-4 <
      (23/10)*(200622323 / 1000000000) := by norm_num
  apply (div_lt_iff₀ ht0).mpr
  linarith only [hb, hn, ht.1]

end GeneralCK.Certificates.SmallMean

import GeneralCK.PsiOuterEntropy200
import GeneralCK.PsiParentPolynomialBounds37

/-! Exact medium-bias parent exclusion at entropy ratio 37. -/

namespace GeneralCK.PsiOuterEntropy37

open GeneralCK.PsiOuterEntropy200

theorem parent_dominance_two_fifths37 {q E : ℝ}
    (hq : 0 < q) (hqu : q ≤ 2 / 5) (hE : 0 < E)
    (hr : 37 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let x := q / E
  have hx : 37 ≤ x := (le_div_iff₀ hE).mpr hr
  have hF := (le_div_iff₀ log_two_pos).mp
    (PsiParentContactEnvelope.F_le_logarithmic_polynomial64 hq hE (by linarith))
  have hp := mul_lt_mul_of_pos_left
    (PsiParentPolynomialBounds.log_P64_lt_five_halves37 hx) hq
  have hs := logarithmic_bias_scale (Q := (2 / 5 : ℝ)) hq.le
    (by norm_num) hqu (show 0 ≤ x by linarith)
  have hs' : (5 / 2) * q * Real.log (1 + 2 * x / 7) ≤
      Real.log (1 + 5 * q ^ 2 / (7 * E)) := by
    convert! hs using 1 <;> dsimp [x] <;> congr 1 <;> ring
  change q * Real.log (1 + (1347 / 128) * x + (3 / 64) * x ^ 2) <
    q * ((5 / 2) * Real.log (1 + 2 * x / 7)) at hp
  apply parent_dominance_of_cost_bound hq (by linarith) hE (by linarith)
  change F q E * Real.log 2 ≤
      q * Real.log (1 + (1347 / 128) * x + (3 / 64) * x ^ 2) at hF
  nlinarith only [hF, hp, hs', sq_nonneg q]

#print axioms parent_dominance_two_fifths37

end GeneralCK.PsiOuterEntropy37

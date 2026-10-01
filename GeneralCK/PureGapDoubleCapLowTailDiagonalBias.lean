import GeneralCK.PureGapDoubleCapLowTailLinearSeparation
import GeneralCK.PureGapDoubleCapOuterSlopeChecker
import GeneralCK.SmallMeanCapTailBounds

/-! Exact cancellation in the double-cap bias expression when the contact
and inverse-entropy biases coincide. This isolates the cost of the true
contact displacement `y-c` in the remaining low-tail sign problem. -/

namespace GeneralCK

open Certificates.Reflection Reflection

theorem doubleCapSlopeBiasExpression_diagonal {y : ℝ}
    (hy : 0 < y) (hy1 : y < 1) :
    doubleCapSlopeBiasExpression y y =
      2 - 2 * y * biasE y /
        ((1 - y ^ 2) * SmallMean.A y * biasB y) := by
  have hgap : 0 < 1 - y ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < 1 - y)
      (by linarith : 0 < 1 + y)]
  have hAlo := SmallMean.A_ge_linear_cubic hy.le hy1
  have hApos : 0 < SmallMean.A y := by
    have hminor : 0 < y + y ^ 3 / 3 := by
      have hp : 0 < y * (1 + y ^ 2 / 3) :=
        mul_pos hy (by positivity)
      nlinarith only [hp]
    exact hminor.trans_le hAlo
  have hB : 0 < biasB y := biasB_pos_wide (by linarith [hy]) hy1
  have hident := biasB_eq_biasE_add (by linarith [hy]) hy1
  unfold doubleCapSlopeBiasExpression
  field_simp [hgap.ne', hApos.ne', hB.ne']
  nlinarith [hident]

#print axioms doubleCapSlopeBiasExpression_diagonal

end GeneralCK

import GeneralCK.PureGapDoubleCapLowTailContactLossBridge
import GeneralCK.PureGapDoubleCapLowTailRatioIncrement

/-! An exact secant estimate for the true-contact loss. It uses the
monotonicity of the logarithmic contact bias instead of a derivative upper
bound, and remains meaningful as both contacts approach one. -/

namespace GeneralCK

open Reflection Certificates.Reflection

theorem doubleCapContactGain_secant_upper {c y : ℝ}
    (hc : 0 < c) (hcy : c ≤ y) (hy1 : y < 1) :
    doubleCapContactGain y - doubleCapContactGain c ≤
      (y ^ 2 - c ^ 2) /
        ((1 - y ^ 2) * (1 - c ^ 2) * biasB y) := by
  have hc1 : c < 1 := hcy.trans_lt hy1
  have hy : 0 < y := hc.trans_le hcy
  have hDy : 0 < 1 - y ^ 2 := by nlinarith
  have hDc : 0 < 1 - c ^ 2 := by nlinarith
  have hBc : 0 < biasB c := biasB_pos hc hc1
  have hBy : 0 < biasB y := biasB_pos hy hy1
  have hB : biasB c ≤ biasB y :=
    biasB_strictMonoOn_positive.monotoneOn
      ⟨hc, hc1⟩ ⟨hy, hy1⟩ hcy
  have hDenOrder : (1 - c ^ 2) * biasB c ≤
      (1 - c ^ 2) * biasB y :=
    mul_le_mul_of_nonneg_left hB hDc.le
  have hDenSmall : 0 < (1 - c ^ 2) * biasB c := mul_pos hDc hBc
  have hDenLarge : 0 < (1 - c ^ 2) * biasB y := mul_pos hDc hBy
  have hContact : c ^ 2 / ((1 - c ^ 2) * biasB y) ≤
      c ^ 2 / ((1 - c ^ 2) * biasB c) := by
    apply (div_le_div_iff₀ hDenLarge hDenSmall).mpr
    exact mul_le_mul_of_nonneg_left hDenOrder (sq_nonneg c)
  have hIdentity :
      y ^ 2 / ((1 - y ^ 2) * biasB y) -
        c ^ 2 / ((1 - c ^ 2) * biasB y) =
      (y ^ 2 - c ^ 2) /
        ((1 - y ^ 2) * (1 - c ^ 2) * biasB y) := by
    field_simp [hDy.ne', hDc.ne', hBy.ne']
    ring
  unfold doubleCapContactGain
  rw [← hIdentity]
  linarith [hContact]

theorem doubleCapSlopeBiasExpression_nonneg_of_secant_loss {c y : ℝ}
    (hc : 0 < c) (hcy : c ≤ y) (hy1 : y < 1)
    (hcheck :
      2 * ((y ^ 2 - c ^ 2) /
        ((1 - y ^ 2) * (1 - c ^ 2) * biasB y)) ≤
        doubleCapSlopeBiasExpression y y) :
    0 ≤ doubleCapSlopeBiasExpression y c := by
  have hLoss := doubleCapContactGain_secant_upper hc hcy hy1
  have hIdentity : doubleCapSlopeBiasExpression y c =
      doubleCapSlopeBiasExpression y y -
        2 * (doubleCapContactGain y - doubleCapContactGain c) := by
    unfold doubleCapSlopeBiasExpression doubleCapContactGain
    ring
  rw [hIdentity]
  linarith only [hLoss, hcheck]

#print axioms doubleCapContactGain_secant_upper
#print axioms doubleCapSlopeBiasExpression_nonneg_of_secant_loss

end GeneralCK

import GeneralCK.PureGapDoubleCapLowTailSeparationQuotient

/-! The checked coupled contact separation is proportional to the low-cap
mean-bias displacement `2m`. The low-slope sign still needs an independent
cancellation estimate. -/

namespace GeneralCK

open Reflection Certificates.Reflection

theorem doubleCapLowTail_bias_separation_linear {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    doubleCapLowTailY m - doubleCapLowTailC m ≤
      (2 * m * (doubleCapLowTailC m) ^ 2 *
        biasE (doubleCapLowTailY m)) /
        ((1 - 2 * m) ^ 2 * biasB (doubleCapLowTailC m)) := by
  have hk : 0 < 1 - 2 * m := by linarith
  have hbetween := doubleCapLowTailC_between hm hmq
  have hc : 0 < doubleCapLowTailC m := hk.trans hbetween.1
  have hc1 : doubleCapLowTailC m < 1 := by
    have hmem := regularContact_mem
      ((1 - 2 * m) / biasE (doubleCapLowTailY m))
    simpa only [doubleCapLowTailC] using hmem.2
  have hB : 0 < biasB (doubleCapLowTailC m) :=
    biasB_pos_wide (by linarith [hc]) hc1
  have hden : 0 < (1 - 2 * m) ^ 2 * biasB (doubleCapLowTailC m) :=
    mul_pos (sq_pos_of_pos hk) hB
  have hh : 0 < H (2 * m) / 2 :=
    div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hh1 : H (2 * m) / 2 < 1 :=
    (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
  have hy1 : doubleCapLowTailY m < 1 := by
    dsimp [doubleCapLowTailY]
    linarith [entropyInverse_pos hh hh1.le]
  have hEy : 0 < biasE (doubleCapLowTailY m) := by
    rw [doubleCapLowTailY_entropy hm hmq]
    exact mul_pos log_two_pos hh
  have hgap : doubleCapLowTailY m - (1 - 2 * m) ≤ 2 * m := by linarith
  have hnum :
      (doubleCapLowTailY m - (1 - 2 * m)) *
      (doubleCapLowTailC m) ^ 2 * biasE (doubleCapLowTailY m) ≤
        2 * m * (doubleCapLowTailC m) ^ 2 *
          biasE (doubleCapLowTailY m) := by
    have hcSq : 0 ≤ (doubleCapLowTailC m) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hgap
      (mul_nonneg hcSq hEy.le)]
  exact (doubleCapLowTail_bias_separation_quotient hm hmq).trans
    (div_le_div_of_nonneg_right hnum hden.le)

#print axioms doubleCapLowTail_bias_separation_linear

end GeneralCK

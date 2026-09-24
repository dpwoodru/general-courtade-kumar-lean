import GeneralCK.PureGapDoubleCapLowTailSeparation

/-! Quotient form of the checked true-contact separation inequality. -/

namespace GeneralCK

open Reflection Certificates.Reflection

theorem doubleCapLowTail_bias_separation_quotient {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    doubleCapLowTailY m - doubleCapLowTailC m ≤
      ((doubleCapLowTailY m - (1 - 2 * m)) *
        (doubleCapLowTailC m) ^ 2 * biasE (doubleCapLowTailY m)) /
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
  apply (le_div_iff₀ hden).mpr
  have hpoly := doubleCapLowTail_bias_separation hm hmq
  nlinarith only [hpoly]

#print axioms doubleCapLowTail_bias_separation_quotient

end GeneralCK

import GeneralCK.PureGapDoubleCapLowTailActualSecant
import GeneralCK.PureGapDoubleCapOuterSlopeChecker

/-! Unconditional sign of the canonical low-cap slope and endpoint residual
in the near-zero interval. -/

namespace GeneralCK

open Reflection Certificates.Reflection

theorem doubleCapLowTail_actual_bias_slope_nonneg {m : ℝ}
    (hm : 0 < m) (hm100 : m ≤ 1 / 100) :
    0 ≤ doubleCapSlopeBiasExpression
      (doubleCapLowTailY m) (doubleCapLowTailC m) := by
  have hmq : m ≤ 1 / 4 := by linarith
  have hBetween := doubleCapLowTailC_between hm hmq
  have hk : 49 / 50 ≤ 1 - 2 * m := by linarith [hm100]
  have hc : 0 < doubleCapLowTailC m := by linarith [hk, hBetween.1]
  have hcy : doubleCapLowTailC m ≤ doubleCapLowTailY m := hBetween.2.le
  have hyHigh : 49 / 50 ≤ doubleCapLowTailY m := by
    linarith [hk, hBetween.1, hBetween.2]
  have hh : 0 < H (2 * m) / 2 :=
    div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hh1 : H (2 * m) / 2 < 1 :=
    (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
  have hy1 : doubleCapLowTailY m < 1 := by
    dsimp [doubleCapLowTailY]
    linarith [entropyInverse_pos hh hh1.le]
  have hLoss := doubleCapLowTail_actual_secant_le_four_thirds hm hm100
  have hDiag := doubleCapLowTail_diagonal_slope_ge_four_thirds hyHigh hy1
  exact doubleCapSlopeBiasExpression_nonneg_of_secant_loss
    hc hcy hy1 (hLoss.trans hDiag)

theorem doubleCapLowSlopeResidual_nonneg_near_zero {m : ℝ}
    (hm : 0 < m) (hm100 : m ≤ 1 / 100) :
    0 ≤ doubleCapLowSlopeResidual m := by
  have hmq : m ≤ 1 / 4 := by linarith
  have hmh : m < 1 / 2 := by linarith
  let h : ℝ := H (2 * m) / 2
  have hh : 0 < h := by
    dsimp [h]
    exact div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hh1 : h < 1 := by
    dsimp [h]
    exact (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
  have hBias0 := four_add_deriv_phi_eq_slopeBias hm hmh hh hh1
  dsimp only at hBias0
  have hBias : 4 + deriv (phi m) h =
      doubleCapSlopeBiasExpression
        (doubleCapLowTailY m) (doubleCapLowTailC m) := by
    change 4 + deriv (phi m) h =
      doubleCapSlopeBiasExpression
        (1 - 2 * entropyInverse h)
        (regularContact (((1 - 2 * m) / h) / Real.log 2)) at hBias0
    have hyEq : 1 - 2 * entropyInverse h = doubleCapLowTailY m := rfl
    have hcEq : regularContact (((1 - 2 * m) / h) / Real.log 2) =
        doubleCapLowTailC m := by
      simpa only [h] using (doubleCapLowTailC_physical hm hmq).symm
    rw [hyEq, hcEq] at hBias0
    exact hBias0
  have hFormula0 := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  have hFormula : 4 + deriv (phi m) h = doubleCapLowSlopeResidual m := by
    simpa only [doubleCapLowSlopeResidual, h] using hFormula0
  linarith only [hBias, hFormula,
    doubleCapLowTail_actual_bias_slope_nonneg hm hm100]

theorem doubleCapLowResidual_nonneg_near_zero {m : ℝ}
    (hm : 0 < m) (hm100 : m ≤ 1 / 100) :
    0 ≤ doubleCapLowResidual m := by
  have hmq : m ≤ 1 / 4 := by linarith
  have hmh : m < 1 / 2 := by linarith
  let h : ℝ := H (2 * m) / 2
  have hh : 0 < h := by
    dsimp [h]
    exact div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hhCap : h < H m := by
    dsimp [h]
    exact doubleCapLowFloor_lt_entropyCap hm hmq
  have hh1 : h < 1 := hhCap.trans_le (H_le_one m)
  have hFormula0 := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  have hFormula : 4 + deriv (phi m) h = doubleCapLowSlopeResidual m := by
    simpa only [doubleCapLowSlopeResidual, h] using hFormula0
  have hDeriv : -4 ≤ deriv (phi m) h := by
    linarith only [hFormula, doubleCapLowSlopeResidual_nonneg_near_zero hm hm100]
  unfold doubleCapLowResidual
  exact doubleCapEndpointResidual_nonneg_of_slope hm hmh hh hhCap hDeriv

#print axioms doubleCapLowTail_actual_bias_slope_nonneg
#print axioms doubleCapLowSlopeResidual_nonneg_near_zero
#print axioms doubleCapLowResidual_nonneg_near_zero

end GeneralCK

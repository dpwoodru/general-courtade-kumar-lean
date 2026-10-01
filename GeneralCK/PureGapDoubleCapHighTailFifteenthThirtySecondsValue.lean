import GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsActualSign

/-! Direct true endpoint-value consequence of the checked `m≥15/32` slope. -/

namespace GeneralCK

theorem doubleCapHighResidual_nonneg_on_fifteenth_tail {m : ℝ}
    (hm15 : 15 / 32 ≤ m) (hmh : m < 1 / 2) :
    0 ≤ doubleCapHighResidual m := by
  have hm : 0 < m := by linarith
  let h : ℝ := (1 + H (2 * m - 1 / 2)) / 2
  have hh : 0 < h := by
    have hx0 : 0 < 2 * m - 1 / 2 := by linarith
    have hx1 : 2 * m - 1 / 2 < 1 := by linarith
    have hH := H_pos hx0 hx1
    dsimp [h]
    linarith
  have hhCap : h < H m := by
    dsimp [h]
    exact doubleCapHighFloor_lt_entropyCap (by linarith) hmh
  have hh1 : h < 1 := hhCap.trans_le (H_le_one m)
  have hSlope := doubleCapHighSlopeResidual_nonneg_on_fifteenth_tail hm15 hmh
  have hFormula := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  have hResidualEq : 4 + deriv (phi m) h = doubleCapHighSlopeResidual m := by
    simpa only [doubleCapHighSlopeResidual, h] using hFormula
  have hDeriv : -4 ≤ deriv (phi m) h := by
    linarith [hResidualEq, hSlope]
  unfold doubleCapHighResidual
  exact doubleCapEndpointResidual_nonneg_of_slope hm hmh hh hhCap hDeriv

theorem doubleCapHighCapEndpoint_on_fifteenth_tail {m : ℝ}
    (hm15 : 15 / 32 ≤ m) (hmh : m < 1 / 2) :
    phi m (capEntropyFloor m) ≤
      4 * (H m - capEntropyFloor m) := by
  have hm : 0 < m := by linarith
  have hh : 0 < (1 + H (2 * m - 1 / 2)) / 2 := by
    have hx0 : 0 < 2 * m - 1 / 2 := by linarith
    have hx1 : 2 * m - 1 / 2 < 1 := by linarith
    linarith [H_pos hx0 hx1]
  have hh1 : (1 + H (2 * m - 1 / 2)) / 2 ≤ 1 := by
    linarith [H_le_one (2 * m - 1 / 2)]
  have hFloor : capEntropyFloor m =
      (1 + H (2 * m - 1 / 2)) / 2 := by
    unfold capEntropyFloor
    simp only [if_neg (by linarith : ¬ m ≤ (1 / 4 : ℝ))]
  rw [hFloor]
  exact (doubleCap_endpoint_iff_residual_nonneg hm hmh hh hh1).2
    (doubleCapHighResidual_nonneg_on_fifteenth_tail hm15 hmh)

#print axioms doubleCapHighResidual_nonneg_on_fifteenth_tail
#print axioms doubleCapHighCapEndpoint_on_fifteenth_tail

end GeneralCK

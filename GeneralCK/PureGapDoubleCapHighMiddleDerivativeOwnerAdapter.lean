import GeneralCK.PureGapDoubleCapHighMiddleDerivativeAggregate

/-! Exact high-middle slope owner adapter, conditional only on future
proof-bearing 256 derivative-cell certificates. -/

namespace GeneralCK
open Certificates.Reflection

/-- On the bridge `m ∈ [2/5,7/16]`, the true slope residual follows from
the checked derivative formula, complete grid, and a future Lean replay of
all 256 positivity cells. -/
theorem doubleCapHighSlopeResidual_nonneg_on_bridge_of_256_cells
    (hCells : ∀ i : Fin 256,
      DoubleCapBridgeDerivativeCellCertificate i
        doubleCapBridgeDerivativeExpression)
    {m : ℝ} (hmLo : 2 / 5 ≤ m) (hmHi : m ≤ 7 / 16) :
    0 ≤ doubleCapHighSlopeResidual m := by
  have hm : 0 < m := by linarith
  have hmh : m < 1 / 2 := by linarith
  let x : ℝ := 1 - 2 * m
  let h : ℝ := (1 + H (2 * m - 1 / 2)) / 2
  have hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ) := by
    dsimp [x]
    constructor <;> linarith
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : x < 1 / 2 := by linarith [hx.2]
  have hfloorEq : h = doubleCapHighTailFloor x := by
    dsimp [h, x, doubleCapHighTailFloor]
    congr 1
    ring
  have hh : 0 < h := by
    rw [hfloorEq]
    exact doubleCapHighTailFloor_pos hx0 hx1
  have hhCap : h < H m := by
    dsimp [h]
    exact doubleCapHighFloor_lt_entropyCap (by linarith) hmh
  have hh1 : h < 1 := hhCap.trans_le (H_le_one m)
  have hYeq : 1 - 2 * entropyInverse h = doubleCapHighTailY x := by
    rw [hfloorEq]
    rfl
  have hCeq : Reflection.regularContact
      (((1 - 2 * m) / h) / Real.log 2) = doubleCapHighTailC x := by
    rw [hfloorEq]
    unfold doubleCapHighTailC
    congr 1
    dsimp [x]
    field_simp [log_two_pos.ne',
      (doubleCapHighTailFloor_pos hx0 hx1).ne']
  have hBias := doubleCapBridgeSlope_nonneg_of_256_cells hCells hx
  have hSlopeBias := four_add_deriv_phi_eq_slopeBias hm hmh hh hh1
  dsimp only at hSlopeBias
  rw [hYeq, hCeq] at hSlopeBias
  have hSlopeFormula := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  have hResidualEq : 4 + deriv (phi m) h = doubleCapHighSlopeResidual m := by
    simpa only [doubleCapHighSlopeResidual, h] using hSlopeFormula
  dsimp only [doubleCapBridgeSlope] at hBias
  linarith

#print axioms doubleCapHighSlopeResidual_nonneg_on_bridge_of_256_cells

end GeneralCK

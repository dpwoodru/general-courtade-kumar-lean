import GeneralCK.PureGapDoubleCapHighMiddleImplicitDerivativeAdapters
import GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsActualSign

/-! Sound bridge aggregation from future proof-bearing 256-cell certificates.
The external Fraction interval table is not imported or trusted. -/

namespace GeneralCK
open Certificates.Reflection

/-- Future Lean cell proofs plus the checked true derivative formula make
the exact double-cap bridge slope strictly increasing in `x`. -/
theorem doubleCapBridgeSlope_strictMonoOn_of_256_cells
    (hCells : ∀ i : Fin 256,
      DoubleCapBridgeDerivativeCellCertificate i
        doubleCapBridgeDerivativeExpression) :
    StrictMonoOn doubleCapBridgeSlope
      (Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) := by
  have hCont : ContinuousOn doubleCapBridgeSlope
      (Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) := by
    intro x hx
    exact (doubleCapBridgeSlope_hasDerivAt_on_high_middle hx).continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hCont
  intro x hx
  exact doubleCapBridge_true_deriv_pos_of_256_cells
    (fun z hz => doubleCapBridgeSlope_hasDerivAt_on_high_middle hz)
    hCells (interior_subset hx)

/-- The checked 7/16 endpoint sign and future 256 Lean derivative cells
imply the exact high-branch slope bias is nonnegative on the bridge. -/
theorem doubleCapBridgeSlope_nonneg_of_256_cells
    (hCells : ∀ i : Fin 256,
      DoubleCapBridgeDerivativeCellCertificate i
        doubleCapBridgeDerivativeExpression)
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    0 ≤ doubleCapBridgeSlope x := by
  have hEndpoint : 0 ≤ doubleCapBridgeSlope (1 / 8 : ℝ) := by
    simpa only [doubleCapBridgeSlope] using
      (doubleCapHighTailSeven_bias_nonneg (x := (1 / 8 : ℝ))
        (by norm_num) (by norm_num))
  by_cases heq : x = (1 / 8 : ℝ)
  · simpa only [heq] using hEndpoint
  · have hlt : (1 / 8 : ℝ) < x := lt_of_le_of_ne hx.1 (Ne.symm heq)
    have hMono := doubleCapBridgeSlope_strictMonoOn_of_256_cells hCells
      (by norm_num : (1 / 8 : ℝ) ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) hx hlt
    exact hEndpoint.trans hMono.le

#print axioms doubleCapBridgeSlope_strictMonoOn_of_256_cells
#print axioms doubleCapBridgeSlope_nonneg_of_256_cells

end GeneralCK

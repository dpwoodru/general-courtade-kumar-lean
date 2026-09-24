import GeneralCK.PureGapDoubleCapHighMiddleDerivativeCoverage
import GeneralCK.ReflectionContactInverse

/-! Sound finite-cell interface for the true high-cap slope derivative.
The explicit derivative identity and 256 cell certificates are hypotheses
until they are separately proved; no external numerical output is trusted. -/

namespace GeneralCK
open Certificates.Reflection

noncomputable def doubleCapBridgeL (x : ℝ) : ℝ :=
  Real.log 2 * doubleCapHighTailFloor x

noncomputable def doubleCapBridgeSlope (x : ℝ) : ℝ :=
  doubleCapSlopeBiasExpression (doubleCapHighTailY x)
    (doubleCapHighTailC x)

noncomputable def doubleCapBridgeDerivativeExpression (x : ℝ) : ℝ :=
  let y := doubleCapHighTailY x;
  let c := doubleCapHighTailC x;
  let ay := SmallMean.A y;
  let ac := SmallMean.A c;
  let a2x := SmallMean.A (2 * x);
  let b := biasB c;
  let e := biasE c;
  let l := doubleCapBridgeL x;
  let dy := (1 - y ^ 2) * ay;
  let dc := (1 - c ^ 2) * b;
  (-2 : ℝ) * (((1 + y ^ 2) * ay - y) / dy ^ 2) * (a2x / ay) +
    2 * (c * (2 * b - c ^ 2) / dc ^ 2) *
      ((e + c * a2x) / (l + x * ac))

/-- Conditional soundness of the exact derivative identity plus complete
256-cell finite certificate replay. The two premises are formal Lean proof
obligations; the external interval probe is not used here. -/
theorem doubleCapBridge_true_deriv_pos_of_256_cells
    (hFormula : ∀ x : ℝ, x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ) →
      HasDerivAt doubleCapBridgeSlope
        (doubleCapBridgeDerivativeExpression x) x)
    (hCells : ∀ i : Fin 256,
      DoubleCapBridgeDerivativeCellCertificate i
        doubleCapBridgeDerivativeExpression)
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    0 < deriv doubleCapBridgeSlope x := by
  rw [(hFormula x hx).deriv]
  exact doubleCapBridge_derivative_pos_of_256_cells hCells hx

#print axioms doubleCapBridge_true_deriv_pos_of_256_cells

end GeneralCK

import GeneralCK.PureGapDoubleCapHighMiddleDerivativeChecker

/-! Factored trace form for generated exact-rational derivative interval proofs.
The equivalence to the true checked derivative expression is a Lean theorem,
so a generator may use whichever algebraic shape is easiest to replay. -/

namespace GeneralCK
open Certificates.Reflection

noncomputable def doubleCapBridgeDerivativeTraceForm (x : ℝ) : ℝ :=
  let y := doubleCapHighTailY x;
  let c := doubleCapHighTailC x;
  let ay := SmallMean.A y;
  let ac := SmallMean.A c;
  let a2 := SmallMean.A (2 * x);
  let b := biasB c;
  let e := biasE c;
  let l := doubleCapBridgeL x;
  let dy := (1 - y * y) * ay;
  let dc := (1 - c * c) * b;
  let yp := a2 / ay;
  let cp := (e + c * a2) / (l + x * ac);
  -2 * (((1 + y * y) * ay - y) / (dy * dy)) * yp +
    2 * (c * (2 * b - c * c) / (dc * dc)) * cp

theorem doubleCapBridgeDerivativeTraceForm_eq (x : ℝ) :
    doubleCapBridgeDerivativeTraceForm x =
      doubleCapBridgeDerivativeExpression x := by
  simp only [doubleCapBridgeDerivativeTraceForm,
    doubleCapBridgeDerivativeExpression, pow_two]

#print axioms doubleCapBridgeDerivativeTraceForm_eq

end GeneralCK

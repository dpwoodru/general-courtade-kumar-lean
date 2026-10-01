import GeneralCK.LogSum
import GeneralCK.PsiEndpointPlaneNoFold

namespace GeneralCK.PsiEndpointPlane

noncomputable def naturalCost (x y : ℝ) : ℝ := Real.log 2 * interiorCost x y

noncomputable def quotient (A B x y : ℝ) : ℝ :=
  (naturalCost x y + A * Real.binEntropy x + B * Real.binEntropy y) / (y - x)

noncomputable def contactLevel1 (A B x y : ℝ) : ℝ :=
  A * Real.log x + B * Real.log y + (x - y) ^ 2 / (2 * x * y)

noncomputable def contactLevel0 (A B x y : ℝ) : ℝ :=
  A * Real.log (1 - x) + B * Real.log (1 - y) + (x - y) ^ 2 / (2 * (1 - x) * (1 - y))

def triangle : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1}

end GeneralCK.PsiEndpointPlane

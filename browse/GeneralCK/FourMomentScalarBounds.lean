import GeneralCK.Reflection
import GeneralCK.CorrectionGlobalConvexity
import GeneralCK.FourMomentLowerBound

namespace GeneralCK.InteriorLaw
open Correction
variable {ι : Type*} [Fintype ι]

/-- All analytic and boundary steps in LB1 are proved. Its three remaining
scalar sign inputs are stated explicitly for certificate replacement. -/
theorem fourMomentLowerBound_le_cost_of_scalar_bounds (μ : InteriorLaw ι)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2)
    (hdet : ∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) :
    fourMomentLowerBound μ.a μ.b μ.e μ.f ≤ μ.cost :=
  μ.fourMomentLowerBound_le_cost
    (fun _ _ hu hu' hv hv' => Reflection.atom_reflection_of_positive_curvature_nonneg href hu hu' hv hv')
    (convexOn_entropyCorrection_square hleft hdet)

end GeneralCK.InteriorLaw

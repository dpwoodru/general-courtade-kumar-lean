import GeneralCK.FourMomentScalarBounds
import GeneralCK.RemainingBellman
import GeneralCK.EqualEntropy

/-!
# Closure of the unrestricted `phi` branch

This file isolates the exact algebraic closure used in the unrestricted
Bellman argument.  The reflection-curvature and correction-minor signs give
the finite-law lower bound `L4 ≤ cost`; the retained pure-gap statement gives
`candidateGap phi ≤ L4`.  Their sum is the `hphi` premise consumed by
`finiteHybridBellman_of_remaining_regions`.

No feasibility region is added to the pointwise theorem below.  The second
theorem merely packages it with exactly the canonical domain appearing in the
remaining-region interface.
-/

namespace GeneralCK

open Correction

namespace InteriorLaw

variable {ι : Type*} [Fintype ι]

/-- Reflection curvature, the two correction Hessian minor signs, and the
pure-gap inequality close the `phi` Bellman branch for any interior law. -/
theorem phi_gap_le_cost_of_scalar_bounds (μ : InteriorLaw ι)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2)
    (hdet : ∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2)
    (hpure : 0 ≤ pureGap μ.a μ.b μ.e μ.f) :
    candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  have hL4 := μ.fourMomentLowerBound_le_cost_of_scalar_bounds href hleft hdet
  unfold pureGap at hpure
  linarith

end InteriorLaw

/-- Package the pointwise closure as exactly the residual `hphi` premise of
the canonical remaining-region theorem. -/
theorem canonical_phi_branch_of_scalar_bounds
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (hpure : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 → μ.e ≠ μ.f →
        0 ≤ pureGap μ.a μ.b μ.e μ.f) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
        candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  intro k μ hab hsum
  exact μ.phi_gap_le_cost_of_scalar_bounds href hleft hdet
    (by
      by_cases hef : μ.e = μ.f
      · rw [hef]
        exact pureGap_equal_entropy_nonneg μ.f_pos μ.a μ.b
      · exact hpure k μ hab hsum hef)

/-- General CK follows once the scalar signs, the canonical pure-gap owner,
and the already-isolated residual active-`psi` region are supplied. -/
theorem generalCourtadeKumar_of_scalar_bounds_and_remaining_regions
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (hpure : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 → μ.e ≠ μ.f →
        0 ≤ pureGap μ.a μ.b μ.e μ.f)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_remaining_regions
    (canonical_phi_branch_of_scalar_bounds href hleft hdet hpure) hpsi

end GeneralCK

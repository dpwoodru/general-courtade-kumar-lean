import GeneralCK.PhiBranchClosure
import GeneralCK.PureGapFixedEntropyClosure

/-!
# Canonical scalar closure of general CK

This packages the exact remaining pure-gap chamber after the proved mean
reflections, label exchange, and entropy rearrangement.  Together with the
three scalar LB-1 signs and the residual active-`psi` owner, it implies the
full general Courtade--Kumar statement.
-/

namespace GeneralCK

/-- General CK from the three LB-1 scalar signs, PG-1 only on its sorted
lower-half marginal-physical chamber, and the residual active-`psi` owner. -/
theorem generalCourtadeKumar_of_canonical_scalar_owners
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (hpure : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ pureGap a c e f)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar := by
  apply generalCourtadeKumar_of_scalar_bounds_and_remaining_regions
    href hleft hdet _ hpsi
  intro k μ hab hsum hef
  exact pureGap_nonneg_of_sorted_lower_half_ordered_entropy_feasible hpure
    μ.a_interior.1.le μ.a_interior.2.le μ.b_interior.1.le μ.b_interior.2.le
    μ.e_pos μ.f_pos μ.e_le_cap μ.f_le_cap

/-- Equivalent end-to-end interface stated with the manuscript's explicit
canonical four-variable gap `G`. -/
theorem generalCourtadeKumar_of_explicit_canonical_owners
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (hG : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ canonicalPureGap a c e f)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar := by
  apply generalCourtadeKumar_of_canonical_scalar_owners href hleft hdet _ hpsi
  intro a c e f ha hac hc he hef hecap hfcap
  rw [pureGap_eq_canonicalPureGap hac hc]
  exact hG a c e f ha hac hc he hef hecap hfcap

/-- End-to-end closure stated with the manuscript's fixed-entropy owner
ledger.  The remaining hypotheses are exactly the reflection curvature,
correction Hessian, retained PG-1 owners, and active-`psi` region. -/
theorem generalCourtadeKumar_of_fixedEntropy_owner_ledger {S : ℝ}
    (hS : S ≤ 1)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (howners : CanonicalPureGapOwners S)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar := by
  apply generalCourtadeKumar_of_canonical_scalar_owners href hleft hdet _ hpsi
  intro a c e f ha hac hc he hef hecap hfcap
  apply pureGap_nonneg_of_canonicalPureGapOwners hS howners
    ha (by linarith) (ha.trans hac) (by linarith) he (he.trans_le hef) hecap hfcap

end GeneralCK

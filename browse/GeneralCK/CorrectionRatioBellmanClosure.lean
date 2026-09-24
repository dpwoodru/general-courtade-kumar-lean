import GeneralCK.CorrectionRatioGlobalBridge
import GeneralCK.CanonicalCKClosure

/-!
# Bellman closure from probability-ratio correction certificates

This removes the coordinate-conversion plumbing between the generated
correction families and the canonical scalar-owner closure.  The correction
premise is stated directly in the `(u, rho)` coordinates checked by those
families and covers the full open probability rectangle.
-/

namespace GeneralCK

/-- General CK from reflection curvature, a full probability-ratio correction
kernel certificate, the canonical pure-gap owner, and the residual active-psi
owner.  No additional domain restriction is introduced. -/
theorem generalCourtadeKumar_of_ratio_kernel_and_canonical_owners
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hkernel : ∀ u rho : ℝ, 0 < u → u < 1/2 → 0 < rho → rho < 1 →
      0 < Correction.Natural.m11 u (u+rho*(1/2-u)) ∧
      0 ≤ Correction.Natural.kdet u (u+rho*(1/2-u)))
    (hpure : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ pureGap a c e f)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar := by
  obtain ⟨hleft, hdet⟩ :=
    Correction.orderedTriangle_signs_of_ratio_kernel hkernel
  exact generalCourtadeKumar_of_canonical_scalar_owners
    href hleft hdet hpure hpsi

/-- Variant matching generated correction leaves, which prove both numerical
minors strictly positive. -/
theorem generalCourtadeKumar_of_strict_ratio_kernel_and_canonical_owners
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hkernel : ∀ u rho : ℝ, 0 < u → u < 1/2 → 0 < rho → rho < 1 →
      0 < Correction.Natural.m11 u (u+rho*(1/2-u)) ∧
      0 < Correction.Natural.kdet u (u+rho*(1/2-u)))
    (hpure : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ pureGap a c e f)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar := by
  apply generalCourtadeKumar_of_ratio_kernel_and_canonical_owners
    href _ hpure hpsi
  intro u rho hu huhalf hr hr1
  exact ⟨(hkernel u rho hu huhalf hr hr1).1,
    (hkernel u rho hu huhalf hr hr1).2.le⟩

/-- End-to-end interface matching the `actual_minors_positive` conclusion of
the generated correction-family aggregate theorem. -/
theorem generalCourtadeKumar_of_actual_ratio_family_and_canonical_owners
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hfamily : ∀ u rho : ℝ, 0 < u → u < 1/2 → 0 < rho → rho < 1 →
      0 < Correction.Mleft (H u) (H (u+rho*(1/2-u))) ∧
      0 < Correction.Mdet (H u) (H (u+rho*(1/2-u))))
    (hpure : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ pureGap a c e f)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar := by
  obtain ⟨hleft, hdet⟩ :=
    Correction.orderedTriangle_signs_of_actual_ratio_family hfamily
  exact generalCourtadeKumar_of_canonical_scalar_owners
    href hleft hdet hpure hpsi

#print axioms generalCourtadeKumar_of_ratio_kernel_and_canonical_owners
#print axioms generalCourtadeKumar_of_strict_ratio_kernel_and_canonical_owners
#print axioms generalCourtadeKumar_of_actual_ratio_family_and_canonical_owners

end GeneralCK

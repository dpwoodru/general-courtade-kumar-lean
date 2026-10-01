import GeneralCK.PsiAnalyticCKClosure
import GeneralCK.PsiGeneralLowEntropy

/-!
# Remaining active-psi owners above the proved entropy cutoff

The canonical low-entropy theorem covers both mean orientations. Therefore
the same-side chart and opposite central owner only need new proofs above
average entropy 10^-6. The opposite compact ledger already has this strict
cutoff. This file makes that reduction explicit in the final CK dependency
interface; it does not assert any remaining owner without a proof.
-/

namespace GeneralCK

def SameSidePsiPositiveEntropyChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    μ.b ≤ 1 / 2 → 1 / 4294967296 < μ.a / μ.b →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

def OppositePsiPositiveEntropyCentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    1 / 2 ≤ μ.b → 1 / 10 ≤ μ.a →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- The compact ledger already explicitly requires E>10^-6. -/
abbrev OppositePsiPositiveEntropyCompactOwner : Prop := OppositePsiCompactOwner

structure ResidualPsiPositiveEntropyRemainingOwners : Prop where
  sameChart : SameSidePsiPositiveEntropyChartOwner
  oppositeCentral : OppositePsiPositiveEntropyCentralOwner
  oppositeCompact : OppositePsiPositiveEntropyCompactOwner

theorem sameSidePsiChartOwner_of_positiveEntropy
    (h : SameSidePsiPositiveEntropyChartOwner) : SameSidePsiChartOwner := by
  intro k μ hab hsum hmean hinfo hside hratio hactive
  by_cases hE : μ.meanEntropy ≤ 1 / 1000000
  · exact PsiGeneralLowEntropy.law_gap_le_cost μ hab hsum hmean hE hactive.le
  · exact h k μ hab hsum hmean hinfo (lt_of_not_ge hE) hside hratio hactive

theorem oppositePsiCentralOwner_of_positiveEntropy
    (h : OppositePsiPositiveEntropyCentralOwner) : OppositePsiCentralOwner := by
  intro k μ hab hsum hmean hinfo hside ha hactive
  by_cases hE : μ.meanEntropy ≤ 1 / 1000000
  · exact PsiGeneralLowEntropy.law_gap_le_cost μ hab hsum hmean hE hactive.le
  · exact h k μ hab hsum hmean hinfo (lt_of_not_ge hE) hside ha hactive

/-- Restore the three original owner domains by applying the checked global
low-entropy theorem wherever the strict entropy cutoff does not hold. -/
theorem ResidualPsiPositiveEntropyRemainingOwners.toAnalyticRemainingOwners
    (h : ResidualPsiPositiveEntropyRemainingOwners) : ResidualPsiAnalyticRemainingOwners where
  sameChart := sameSidePsiChartOwner_of_positiveEntropy h.sameChart
  oppositeCentral := oppositePsiCentralOwner_of_positiveEntropy h.oppositeCentral
  oppositeCompact := h.oppositeCompact

theorem residualPsi_of_positive_entropy_remaining_owners
    (h : ResidualPsiPositiveEntropyRemainingOwners) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_analytic_remaining_owners h.toAnalyticRemainingOwners

theorem finiteHybridBellman_of_phi_and_positive_entropy_psi
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 → candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ResidualPsiPositiveEntropyRemainingOwners) : FiniteHybridBellman :=
  finiteHybridBellman_of_phi_and_remaining_psi hphi hpsi.toAnalyticRemainingOwners

/-- The approved CK target now needs only the unequal-mean phi input and
three active-psi chart inputs with average entropy strictly above 10^-6. -/
theorem generalCourtadeKumar_of_phi_and_positive_entropy_psi
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 → candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ResidualPsiPositiveEntropyRemainingOwners) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_phi_and_remaining_psi hphi hpsi.toAnalyticRemainingOwners

end GeneralCK

#print axioms GeneralCK.sameSidePsiChartOwner_of_positiveEntropy
#print axioms GeneralCK.oppositePsiCentralOwner_of_positiveEntropy
#print axioms GeneralCK.ResidualPsiPositiveEntropyRemainingOwners.toAnalyticRemainingOwners
#print axioms GeneralCK.residualPsi_of_positive_entropy_remaining_owners
#print axioms GeneralCK.finiteHybridBellman_of_phi_and_positive_entropy_psi
#print axioms GeneralCK.generalCourtadeKumar_of_phi_and_positive_entropy_psi

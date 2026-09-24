import GeneralCK.RemainingBellman

/-!
# Exact ledger for the residual active-psi region

This file records the exhaustive mean/entropy split used in Sections 7--8 of
the integrated manuscript.  It turns the single opaque `hpsi` premise into
the four opposite-side certificate owners and the two same-side owners that
the delivered certificates actually establish.
-/

namespace GeneralCK

/-- The uniform same-side small-ratio tail, restricted to the residual
active-psi domain left after the already-proved small-mean and
low-information regions. -/
def SameSidePsiRatioTailOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    μ.b ≤ 1 / 2 → μ.a / μ.b ≤ 1 / 4294967296 →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- The finite same-side chart after removing the ratio tail.  Its source
coordinates are `(-log₂(a/b), b, E/C₀)` on
`[0,32] × [1/32,1/2] × [0,1]`. -/
def SameSidePsiChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    μ.b ≤ 1 / 2 → 1 / 4294967296 < μ.a / μ.b →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- Central opposite-side means, owned by the retained central square. -/
def OppositePsiCentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 2 ≤ μ.b → 1 / 10 ≤ μ.a →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- The extreme opposite-side strip `a ≤ 2⁻²⁸`. -/
def OppositePsiBoundaryOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 2 ≤ μ.b → μ.a ≤ 1 / 268435456 →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- The opposite deterministic corner `a + 1 - b ≤ 2⁻¹³`. -/
def OppositePsiCornerOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 2 ≤ μ.b → μ.a + 1 - μ.b ≤ 1 / 8192 →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- The global low-average-entropy owner `E ≤ 10⁻⁶`. -/
def OppositePsiLowEntropyOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 2 ≤ μ.b → μ.meanEntropy ≤ 1 / 1000000 →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- The exact remaining compact opposite-side chart, after the central
square, boundary strip, deterministic corner, and low-entropy owner have
been removed. -/
def OppositePsiCompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 2 ≤ μ.b →
    1 / 268435456 < μ.a → μ.a < 1 / 10 →
    1 / 8192 < μ.a + 1 - μ.b →
    1 / 1000000 < μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

structure ResidualPsiCertificateOwners : Prop where
  sameRatioTail : SameSidePsiRatioTailOwner
  sameChart : SameSidePsiChartOwner
  oppositeCentral : OppositePsiCentralOwner
  oppositeBoundary : OppositePsiBoundaryOwner
  oppositeCorner : OppositePsiCornerOwner
  oppositeLowEntropy : OppositePsiLowEntropyOwner
  oppositeCompact : OppositePsiCompactOwner

/-- The manuscript's final regional split is exhaustive on the canonical
residual active-psi domain.  All boundary equalities are deliberately owned
by one of the closed regions. -/
theorem residualPsi_of_certificateOwners
    (h : ResidualPsiCertificateOwners) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost := by
  intro k μ hab hsum hmean hinfo hactive
  by_cases hside : μ.b ≤ 1 / 2
  · by_cases hratio : μ.a / μ.b ≤ 1 / 4294967296
    · exact h.sameRatioTail k μ hab hsum hmean hinfo hside hratio hactive
    · exact h.sameChart k μ hab hsum hmean hinfo hside
        (lt_of_not_ge hratio) hactive
  · have hopp : 1 / 2 ≤ μ.b := (lt_of_not_ge hside).le
    by_cases hcentral : 1 / 10 ≤ μ.a
    · exact h.oppositeCentral k μ hab hsum hmean hinfo hopp hcentral hactive
    · have haSmall : μ.a < 1 / 10 := lt_of_not_ge hcentral
      by_cases hboundary : μ.a ≤ 1 / 268435456
      · exact h.oppositeBoundary k μ hab hsum hmean hinfo hopp hboundary hactive
      · have haLarge : 1 / 268435456 < μ.a := lt_of_not_ge hboundary
        by_cases hcorner : μ.a + 1 - μ.b ≤ 1 / 8192
        · exact h.oppositeCorner k μ hab hsum hmean hinfo hopp hcorner hactive
        · have hnotCorner : 1 / 8192 < μ.a + 1 - μ.b := lt_of_not_ge hcorner
          by_cases hlow : μ.meanEntropy ≤ 1 / 1000000
          · exact h.oppositeLowEntropy k μ hab hsum hmean hinfo hopp hlow hactive
          · exact h.oppositeCompact k μ hab hsum hmean hinfo hopp haLarge haSmall
              hnotCorner (lt_of_not_ge hlow) hactive

end GeneralCK

import CKLaneM1.MLChecker

/-!
# Lane M1: canonical-row form of the same-side leaf statement

The scope-locked manuscript rows (`coord/routesrc/CKRoute/Manuscript.lean`, e.g. `SS_Compact`) are stated for
canonical laws `a ≤ b` with STRICT psi-activity.  `SemSS` (checker soundness) assumes `a < b` and non-strict
activity; the diagonal `a = b` is closed here directly (zero Jensen gap: `splitBound = 0 = psiLogSumCostFloor`),
exactly as `same_side/PROOF.md` §2 ("the exact diagonal x=0 has Delta=0").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM1.ML

open GeneralCK

/-- Diagonal laws: the psi candidate is dominated by the (zero) log-sum floor. -/
theorem gap_le_cost_of_diag {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a = μ.b)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost := by
  have hmid : μ.midpoint = μ.a := by
    unfold InteriorLaw.midpoint
    rw [hab]
    ring
  have hΔ : μ.entropyDrop = 0 := by
    unfold InteriorLaw.entropyDrop
    rw [hmid, hab]
    ring
  have hsplit : μ.splitBound = 0 := by
    unfold InteriorLaw.splitBound
    rw [hΔ, zero_add, sub_self]
  have hfloor : μ.psiLogSumCostFloor = 0 := by
    unfold InteriorLaw.psiLogSumCostFloor interiorCost
    rw [hab]
    ring
  apply μ.gap_le_of_splitBound hact
  rw [hsplit, ← hfloor]
  exact μ.psiLogSumCostFloor_le_cost

/-- Canonical-row form of the leaf statement: `a ≤ b` and strict psi-activity (BRIEF §7). -/
def SemSSRow (B : SSBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → InSS B μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem semSSRow_of_semSS {B : SSBox} (h : SemSS B) : SemSSRow B := by
  intro k μ hab hin hact
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact h k μ hlt hin hact.le
  · exact gap_le_cost_of_diag μ heq hact.le

/-- Checker soundness in the canonical-row form. -/
theorem checkLeaf_sound_row {p : List ℕ} {w : LeafCert} (h : checkLeaf p w = true) :
    SemSSRow (ssBox p) :=
  semSSRow_of_semSS (checkLeaf_sound h)

end CKLaneM1.ML

import CKLaneN4.GlobalEight
import CKLaneN4.ParentTheorems

/-!
# Lane N4: the outer opposite-side low-entropy corollary (`OP_LowEntropy25`)

Archive: CK_GENERAL_COMPLETION `reduction/eight_global/OUTER_OPPOSITE_LOW_ENTROPY.md`:
every positive feasible opposite-side tuple with a mean outside `[1/10, 9/10]` and `E ≤ 1/25`
satisfies `ζ ≥ R_max`.  Canonical form (`a ≤ b`, `a + b ≤ 1`, `b ≥ 1/2`, `a < 1/10`) with strict
psi-activity, as the route's rows.

Proof exactly as archived.  `q = 1 - a - b ∈ [0, 1/2)`, `d = b - a ≥ 2/5 > 8/25 ≥ 8E`.
* `q = 0`: exact parent equality `phi(1/2, E) = psi(1/2, E)` (no strict activity);
* `0 < q ≤ 2/5`, `q ≥ 8E`: PARENT8 (`parent8`) — no strict activity;
* `0 < q ≤ 2/5`, `q ≤ 8E`: global cap-free eight-ratio theorem (`globalEightPsi_law`, `E ≤ 11/200`);
* `2/5 ≤ q ≤ 1/2`, `E ≤ 1/40`: `q/E ≥ 16`, PARENT16 (`parent16`) — no strict activity;
* `2/5 ≤ q ≤ 1/2`, `1/40 ≤ E ≤ 1/25`: HIGH_Q_PARENT (`highQParent`) — no strict activity.
-/

namespace CKLaneN4

open GeneralCK

/-- Strict psi-activity at the parent (verbatim copy of `CKRoute.PsiActive`). -/
def PsiActive {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy

/-- The outer opposite-side low-entropy corollary through `E = 1/25`, canonical form. -/
def OP_LowEntropy25 : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b →
    μ.a < 1 / 10 → μ.meanEntropy ≤ 1 / 25 →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-- Exact parent equality on the `q = 0` face. -/
theorem phi_eq_psi_half (E : ℝ) : phi (1 / 2) E = psi (1 / 2) E := by
  unfold phi psi
  norm_num [F, H_half]

theorem opLowEntropy25 : OP_LowEntropy25 := by
  intro k μ hab hsum hb ha hE25 hact
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hmid : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint; ring
  have hact' : phi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy <
      psi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy := by rwa [hmid]
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hd8 : 8 * μ.meanEntropy ≤ μ.b - μ.a := by linarith
  rcases hq0.eq_or_lt with hz | hqpos
  · exfalso
    have h2 : (1 - (1 - μ.a - μ.b)) / 2 = 1 / 2 := by rw [← hz]; norm_num
    rw [h2, phi_eq_psi_half] at hact'
    exact lt_irrefl _ hact'
  by_cases hq25 : 1 - μ.a - μ.b ≤ 2 / 5
  · by_cases h8 : 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b
    · exact absurd (parent8 _ _ hE hqpos hq25 h8) (not_lt.mpr hact'.le)
    · exact globalEightPsi_law μ hsum (by linarith) hd8 (lt_of_not_ge h8).le hact.le
  · by_cases hE40 : μ.meanEntropy ≤ 1 / 40
    · exact absurd (parent16 _ _ hE hqpos (by linarith) (by linarith)) (not_lt.mpr hact'.le)
    · exact absurd (highQParent _ _ (by linarith) (by linarith) (by linarith) hE25)
        (not_lt.mpr hact'.le)

/-- The same statement with the local `PsiActive` predicate (route form). -/
theorem opLowEntropy25' : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 2 ≤ μ.b → μ.a < 1 / 10 → μ.meanEntropy ≤ 1 / 25 → PsiActive μ → μ.gap ≤ μ.cost :=
  opLowEntropy25

end CKLaneN4

import CKLaneN4.Parent8Tree
import CKLaneN4.Parent16Tree
import CKLaneN4.HighQTree
import GeneralCK.PsiParentDominance
import GeneralCK.PsiOuterEntropy28
import GeneralCK.PsiOuterEntropy200

/-!
# Lane N4: the parent-dominance theorems PARENT8, PARENT16 and HIGH_Q_PARENT

* `parent8` (CK_OPPOSITE_EXTENSION `audit/PARENT8_PROOF.md`): `0 < q ≤ 2/5`, `q/E ≥ 8` ⇒ `phi > psi`.
  Proof exactly as archived: `q ≤ 1/10` is Theorem C of CK_NO_SEPARATION_EXTENSION
  (`PsiParentDominance.parent_dominance_ratio8_small_bias`); the compact rectangle
  `[1/10, 2/5] × [8, 32]` is the archived 332-leaf partition (`Parent8Tree.sem_root`); the unbounded
  tail `x ≥ 32` is analytic (here `PsiOuterEntropy28.parent_dominance_two_fifths28`, `x ≥ 28`).
* `parent16` (CK_GENERAL_COMPLETION `parent/PARENT16_PROOF.md`): `0 < q ≤ 1/2`, `q/E ≥ 16` ⇒
  `phi > psi`: PARENT8 for `q ≤ 2/5`, the archived 69-leaf partition of `[2/5,1/2] × [16,128]`
  (`Parent16Tree.sem_root`), analytic tail `x ≥ 128` (here `PsiOuterEntropy200.parent_dominance_half`,
  `x ≥ 75`).
* `highQParent` (`reduction/eight_global/HIGH_Q_PARENT.py`): `2/5 ≤ q ≤ 1/2`, `1/40 ≤ E ≤ 1/25` ⇒
  `phi > psi`: the archived 59-leaf partition (`HighQTree.sem_root`).

`q` is the parent bias `|1 - 2m|`, the parent mean is `m = (1 - q)/2`.
-/

namespace CKLaneN4

open GeneralCK

/-- PARENT8: factor-eight parent dominance for `0 < q ≤ 2/5`. -/
def Parent8 : Prop :=
  ∀ q E : ℝ, 0 < E → 0 < q → q ≤ 2 / 5 → 8 * E ≤ q →
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E

/-- PARENT16: factor-sixteen parent dominance for `0 < q ≤ 1/2`. -/
def Parent16 : Prop :=
  ∀ q E : ℝ, 0 < E → 0 < q → q ≤ 1 / 2 → 16 * E ≤ q →
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E

/-- HIGH_Q_PARENT: parent dominance on `2/5 ≤ q ≤ 1/2`, `1/40 ≤ E ≤ 1/25`. -/
def HighQParent : Prop :=
  ∀ q E : ℝ, 2 / 5 ≤ q → q ≤ 1 / 2 → 1 / 40 ≤ E → E ≤ 1 / 25 →
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E

theorem parent8 : Parent8 := by
  intro q E hE hq hq25 h8
  by_cases h10 : q ≤ 1 / 10
  · exact PsiParentDominance.parent_dominance_ratio8_small_bias hE hq h10 h8
  by_cases h32 : 32 * E ≤ q
  · exact PsiOuterEntropy28.parent_dominance_two_fifths28 hq hq25 hE (by linarith)
  · have h := Parent8Tree.sem_root
    simp only [SemQX, Parent8Tree.root] at h
    exact h q E hE (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith)

theorem parent16 : Parent16 := by
  intro q E hE hq hq12 h16
  by_cases h25 : q ≤ 2 / 5
  · exact parent8 q E hE hq h25 (by linarith)
  by_cases h128 : 128 * E ≤ q
  · exact PsiOuterEntropy200.parent_dominance_half (by linarith) hq12 hE (by linarith)
  · have h := Parent16Tree.sem_root
    simp only [SemQX, Parent16Tree.root] at h
    exact h q E hE (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith)

theorem highQParent : HighQParent := by
  intro q E h1 h2 h3 h4
  have h := HighQTree.sem_root
  simp only [SemQE, HighQTree.root] at h
  exact h q E (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith)

/-- Mean form of PARENT8 (any parent mean `m`, bias `|1 - 2m|`). -/
theorem parent8_mean {m E : ℝ} (hE : 0 < E) (hq : 0 < |1 - 2 * m|) (hq25 : |1 - 2 * m| ≤ 2 / 5)
    (h8 : 8 * E ≤ |1 - 2 * m|) : psi m E < phi m E := by
  have h := parent8 _ E hE hq hq25 h8
  rcases le_total 0 (1 - 2 * m) with hs | hs
  · rw [abs_of_nonneg hs] at h
    simpa only [show (1 - (1 - 2 * m)) / 2 = m by ring] using h
  · rw [abs_of_nonpos hs] at h
    have e : (1 - -(1 - 2 * m)) / 2 = 1 - m := by ring
    rw [e] at h
    unfold phi psi at h ⊢
    rwa [H_complement, show |1 - 2 * (1 - m)| = |1 - 2 * m| by
      rw [show 1 - 2 * (1 - m) = -(1 - 2 * m) by ring, abs_neg]] at h

end CKLaneN4

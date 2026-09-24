import CKLaneA.Cell

/-!
# Lane A4: Real-level cover combinators for Lane A's cell checker

`Covered u0 u1 r0 r1` is exactly the conclusion of Lane A's `CKLaneA.Cell.cellOK_sound` on the
rational box `[u0,u1] × [r0,r1]`.  Each certificate cell is proved by its OWN kernel evaluation
(`cellOK … = true := by decide +kernel`), and cells are glued by the two guillotine split lemmas
below, so no Boolean tree is ever evaluated in the kernel.
-/

namespace CKLaneA4.D2
open CKLaneA.Cell CKLaneA.Prog

/-- positivity of both program outputs (`D` and `m11` in probability-ratio coordinates) on a box -/
def Covered (u0 u1 r0 r1 : ℚ) : Prop :=
  ∀ ⦃a z : ℝ⦄, (u0 : ℝ) ≤ a → a ≤ (u1 : ℝ) → (r0 : ℝ) ≤ z → z ≤ (r1 : ℝ) →
    0 < r147_D a z ∧ 0 < r170_M a z

theorem covered_of_cellOK {u0 u1 r0 r1 : ℚ} {d : CellData} (h : cellOK u0 u1 r0 r1 d = true) :
    Covered u0 u1 r0 r1 := by
  intro a z h1 h2 h3 h4
  exact cellOK_sound h h1 h2 h3 h4

theorem covered_of_treeOK {u0 u1 r0 r1 : ℚ} {T : Tree} (h : treeOK u0 u1 r0 r1 T = true) :
    Covered u0 u1 r0 r1 := by
  intro a z h1 h2 h3 h4
  exact treeOK_sound T h h1 h2 h3 h4

theorem Covered.su {u0 u1 r0 r1 : ℚ} (m : ℚ) (hl : Covered u0 m r0 r1) (hr : Covered m u1 r0 r1) :
    Covered u0 u1 r0 r1 := by
  intro a z h1 h2 h3 h4
  rcases le_total a (m : ℝ) with h | h
  · exact hl h1 h h3 h4
  · exact hr h h2 h3 h4

theorem Covered.sr {u0 u1 r0 r1 : ℚ} (m : ℚ) (hl : Covered u0 u1 r0 m) (hr : Covered u0 u1 m r1) :
    Covered u0 u1 r0 r1 := by
  intro a z h1 h2 h3 h4
  rcases le_total z (m : ℝ) with h | h
  · exact hl h1 h2 h3 h
  · exact hr h1 h2 h h4

theorem Covered.apply {u0 u1 r0 r1 : ℚ} (h : Covered u0 u1 r0 r1) {a z : ℝ}
    (h1 : (u0 : ℝ) ≤ a) (h2 : a ≤ (u1 : ℝ)) (h3 : (r0 : ℝ) ≤ z) (h4 : z ≤ (r1 : ℝ)) :
    0 < r147_D a z ∧ 0 < r170_M a z := by
  unfold Covered at h
  exact h h1 h2 h3 h4

end CKLaneA4.D2

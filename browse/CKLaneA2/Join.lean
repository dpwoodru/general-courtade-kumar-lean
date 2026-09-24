import CKLaneA.Cell

/-!
# Lane A2: join lemmas for Lane A's guillotine-tree checker `CKLaneA.Cell.treeOK`

Each certificate cell is checked in its own declaration (`decide +kernel`, fresh kernel cache);
internal tree nodes are assembled with these two lemmas, whose split side conditions are
closed by `decide +kernel` on rational literals.
-/

namespace CKLaneA2
open CKLaneA.Cell

theorem treeOK_su {u0 u1 r0 r1 m : ℚ} {l r : Tree}
    (hm : (decide (u0 ≤ m) && decide (m ≤ u1)) = true)
    (hl : treeOK u0 m r0 r1 l = true) (hr : treeOK m u1 r0 r1 r = true) :
    treeOK u0 u1 r0 r1 (.su m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

theorem treeOK_sr {u0 u1 r0 r1 m : ℚ} {l r : Tree}
    (hm : (decide (r0 ≤ m) && decide (m ≤ r1)) = true)
    (hl : treeOK u0 u1 r0 m l = true) (hr : treeOK u0 u1 m r1 r = true) :
    treeOK u0 u1 r0 r1 (.sr m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

end CKLaneA2

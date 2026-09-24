import CKLaneG3.SCover
import CKLaneG3.Consume

/-!
# Lane G3: same-side cover and the `SS_Compact` row from per-leaf obligations (any halving tree)

* `sCoverR` / `sCover_of_tree`: for ANY halving tree `T : CKLaneD.PTree` (digits `2·axis + side`),
  every law of the `SS_Compact` row lies in the physical image `InS (sBox q.1)` of some leaf `q` of `T`
  (the tree is only a certificate of how the root box is subdivided).
* `ssCompact_of_tree_leaves`: `SLeafOK` on every leaf box of `T` gives `SSCompactRow`
  (verbatim copy of `CKRoute.SS_Compact`).  Specialised to the canonical archived tree in
  `CKLaneG3.S.Compact` (`sTree_cover`, `ssCompact_of_leaves`).
-/

set_option autoImplicit false

namespace CKLaneG3

open CKLaneD GeneralCK

theorem sCoverR : ∀ (T : PTree) (rpre : List ℕ) {a b E : ℝ}, InS (sBox rpre.reverse) a b E →
    ∃ q ∈ T.leavesR rpre, InS (sBox q.1) a b E
  | .leaf l, rpre, a, b, E, h => ⟨(rpre.reverse, l), by simp [PTree.leavesR], h⟩
  | .node ax l r, rpre, a, b, E, h => by
      rcases inS_step _ ax h with h' | h'
      · rw [← sBox_append, ← List.reverse_cons] at h'
        obtain ⟨q, hq, hq'⟩ := sCoverR l (2 * ax :: rpre) h'
        exact ⟨q, by simp only [PTree.leavesR, List.mem_append]; exact Or.inl hq, hq'⟩
      · rw [← sBox_append, ← List.reverse_cons] at h'
        obtain ⟨q, hq, hq'⟩ := sCoverR r ((2 * ax + 1) :: rpre) h'
        exact ⟨q, by simp only [PTree.leavesR, List.mem_append]; exact Or.inr hq, hq'⟩

/-- Every law of the `SS_Compact` row lies in the image of some leaf of any halving tree. -/
theorem sCover_of_tree (T : PTree) {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b)
    (hb : μ.b ≤ 1 / 2) (hm : 1 / 16 < μ.a + μ.b) (hr : 1 / 4294967296 < μ.a / μ.b) :
    ∃ q ∈ T.leaves, InS (sBox q.1) μ.a μ.b μ.meanEntropy :=
  sCoverR T [] (inS_sRoot μ hab hb hm hr)

/-- The `SS_Compact` row from the per-leaf obligation on every leaf box of a halving tree. -/
theorem ssCompact_of_tree_leaves (T : PTree) (h : ∀ q ∈ T.leaves, SLeafOK (sBox q.1)) :
    SSCompactRow := by
  intro k μ hab hb hm hr hact
  obtain ⟨q, hq, hin⟩ := sCover_of_tree T μ hab hb hm hr
  exact h q hq k μ hab hb hm hr hin hact

end CKLaneG3

import CKLaneM06.Semantics

/-!
# Lane M06: subtree aggregation over the archived exact-halving tree

`pathBox (p ++ [d]) = step (pathBox p) d`, and the two children `2a`, `2a+1` of a node cover its
box (closed halves).  Hence a method conclusion proved on both children holds on the parent box
(`ParentDominance.merge`); iterating gives the conclusion on every maximal archived subtree whose
leaves are all certified.
-/

set_option autoImplicit false

namespace CKLaneM06

theorem pathBox_append_single (p : List ℕ) (d : ℕ) : pathBox (p ++ [d]) = step (pathBox p) d := by
  simp only [pathBox, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The two archived children of a box cover it. -/
theorem Box.mem_step {B : Box} {x y z : ℝ} (h : B.Mem x y z) (a : ℕ) (ha : a < 3) :
    (step B (2 * a)).Mem x y z ∨ (step B (2 * a + 1)).Mem x y z := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rcases a with _ | _ | _ | a
  · show (step B 0).Mem x y z ∨ (step B 1).Mem x y z
    rcases le_total x (((B.lo0 + B.hi0) / 2 : ℚ) : ℝ) with hc | hc
    · exact Or.inl ⟨h1, hc, h3, h4, h5, h6⟩
    · exact Or.inr ⟨hc, h2, h3, h4, h5, h6⟩
  · show (step B 2).Mem x y z ∨ (step B 3).Mem x y z
    rcases le_total y (((B.lo1 + B.hi1) / 2 : ℚ) : ℝ) with hc | hc
    · exact Or.inl ⟨h1, h2, h3, hc, h5, h6⟩
    · exact Or.inr ⟨h1, h2, hc, h4, h5, h6⟩
  · show (step B 4).Mem x y z ∨ (step B 5).Mem x y z
    rcases le_total z (((B.lo2 + B.hi2) / 2 : ℚ) : ℝ) with hc | hc
    · exact Or.inl ⟨h1, h2, h3, h4, h5, hc⟩
    · exact Or.inr ⟨h1, h2, h3, h4, hc, h6⟩
  · omega

/-- Parent dominance on both archived children gives parent dominance on the parent box. -/
theorem ParentDominance.merge {p : List ℕ} {a : ℕ} (ha : a < 3)
    (h0 : ParentDominance (pathBox (p ++ [2 * a])))
    (h1 : ParentDominance (pathBox (p ++ [2 * a + 1]))) :
    ParentDominance (pathBox p) := by
  intro k μ hB
  rcases Box.mem_step hB a ha with h | h
  · exact h0 k μ (by rw [pathBox_append_single]; exact h)
  · exact h1 k μ (by rw [pathBox_append_single]; exact h)

end CKLaneM06

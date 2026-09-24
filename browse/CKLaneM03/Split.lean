import CKLaneM03.Kernel

/-!
# Lane M03: archived-subtree aggregation lemmas

`Sem` of the two halves of an archived bisection gives `Sem` of the parent box
(`ssBox (p ++ [2k])`, `ssBox (p ++ [2k+1])` are the exact `COVER.split` halves of `ssBox p`),
and list-membership helpers for per-shard root families.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM03

open GeneralCK

theorem ssBox_append (p : List ℕ) (d : ℕ) : ssBox (p ++ [d]) = ssStep (ssBox p) d := by
  simp only [ssBox, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem sem_split_x {X : SBox} (h0 : Sem (ssStep X 0)) (h1 : Sem (ssStep X 1)) : Sem X := by
  intro k μ hbox
  unfold InSBox at hbox
  obtain ⟨hx1, hx2, hb1, hb2, hE1, hE2⟩ := hbox
  rcases le_total ((2 : ℝ) ^ (-(((X.xlo + X.xhi) / 2 : ℚ) : ℝ))) (μ.a / μ.b) with h | h
  · exact h0 k μ ⟨h, hx2, hb1, hb2, hE1, hE2⟩
  · exact h1 k μ ⟨hx1, h, hb1, hb2, hE1, hE2⟩

theorem sem_split_b {X : SBox} (h0 : Sem (ssStep X 2)) (h1 : Sem (ssStep X 3)) : Sem X := by
  intro k μ hbox
  unfold InSBox at hbox
  obtain ⟨hx1, hx2, hb1, hb2, hE1, hE2⟩ := hbox
  rcases le_total μ.b (((X.blo + X.bhi) / 2 : ℚ) : ℝ) with h | h
  · exact h0 k μ ⟨hx1, hx2, hb1, h, hE1, hE2⟩
  · exact h1 k μ ⟨hx1, hx2, h, hb2, hE1, hE2⟩

theorem sem_split_t {X : SBox} (h0 : Sem (ssStep X 4)) (h1 : Sem (ssStep X 5)) : Sem X := by
  intro k μ hbox
  unfold InSBox at hbox
  obtain ⟨hx1, hx2, hb1, hb2, hE1, hE2⟩ := hbox
  rcases le_total μ.meanEntropy
      ((((X.tlo + X.thi) / 2 : ℚ) : ℝ) * ((H μ.a + H μ.b) / 2)) with h | h
  · exact h0 k μ ⟨hx1, hx2, hb1, hb2, hE1, h⟩
  · exact h1 k μ ⟨hx1, hx2, hb1, hb2, h, hE2⟩

theorem sem_node_x (p : List ℕ) (h0 : Sem (ssBox (p ++ [0]))) (h1 : Sem (ssBox (p ++ [1]))) :
    Sem (ssBox p) := by
  rw [ssBox_append] at h0 h1
  exact sem_split_x h0 h1

theorem sem_node_b (p : List ℕ) (h0 : Sem (ssBox (p ++ [2]))) (h1 : Sem (ssBox (p ++ [3]))) :
    Sem (ssBox p) := by
  rw [ssBox_append] at h0 h1
  exact sem_split_b h0 h1

theorem sem_node_t (p : List ℕ) (h0 : Sem (ssBox (p ++ [4]))) (h1 : Sem (ssBox (p ++ [5]))) :
    Sem (ssBox p) := by
  rw [ssBox_append] at h0 h1
  exact sem_split_t h0 h1

theorem sem_forall_cons {q : List ℕ} {l : List (List ℕ)} (h : Sem (ssBox q))
    (hl : ∀ x ∈ l, Sem (ssBox x)) : ∀ x ∈ q :: l, Sem (ssBox x) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h
  · exact hl x hx

theorem sem_forall_nil : ∀ x ∈ ([] : List (List ℕ)), Sem (ssBox x) := by
  intro x hx
  simp at hx

theorem sem_forall_append {l₁ l₂ : List (List ℕ)} (h₁ : ∀ x ∈ l₁, Sem (ssBox x))
    (h₂ : ∀ x ∈ l₂, Sem (ssBox x)) : ∀ x ∈ l₁ ++ l₂, Sem (ssBox x) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h₁ x hx
  · exact h₂ x hx

end CKLaneM03

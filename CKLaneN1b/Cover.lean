import CKLaneN1b.Tree
import CKLaneN1b.Analytic

/-!
# Coverage of the moderate-entropy domain by the archived partition tree

`modTree_cover`: every interior law with `1/10 ≤ a ≤ 1/2`, `1/2 ≤ b ≤ 9/10` and
`11/200 ≤ E` lies in the exact image `InBox (boxOf q.1)` of some leaf `q` of the archived tree
(any owner label), with the archived coordinate map `E = 11/200 + t (C0 - 11/200)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN1b

open GeneralCK

/-- A real point of `(a, b, t)` space lies in a box. -/
def PtIn (B : Box) (a b t : ℝ) : Prop :=
  (B.a0 : ℝ) ≤ a ∧ a ≤ (B.a1 : ℝ) ∧ (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
    (B.t0 : ℝ) ≤ t ∧ t ≤ (B.t1 : ℝ)

theorem boxOf_append (p : List ℕ) (d : ℕ) : boxOf (p ++ [d]) = boxStep (boxOf p) d := by
  unfold boxOf
  rw [List.foldl_append]
  rfl

theorem ptIn_step {B : Box} {a b t : ℝ} (h : PtIn B a b t) (ax : ℕ) :
    PtIn (boxStep B (2 * ax)) a b t ∨ PtIn (boxStep B (2 * ax + 1)) a b t := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rcases ax with _ | _ | _ | ax
  · rcases le_total a (((B.a0 + B.a1) / 2 : ℚ) : ℝ) with hm | hm
    · left; exact ⟨h1, hm, h3, h4, h5, h6⟩
    · right; exact ⟨hm, h2, h3, h4, h5, h6⟩
  · rcases le_total b (((B.b0 + B.b1) / 2 : ℚ) : ℝ) with hm | hm
    · left; exact ⟨h1, h2, h3, hm, h5, h6⟩
    · right; exact ⟨h1, h2, hm, h4, h5, h6⟩
  · rcases le_total t (((B.t0 + B.t1) / 2 : ℚ) : ℝ) with hm | hm
    · left; exact ⟨h1, h2, h3, h4, h5, hm⟩
    · right; exact ⟨h1, h2, h3, h4, hm, h6⟩
  · left
    have e : 2 * (ax + 3) = 2 * ax + 6 := by ring
    simp only [boxStep, e]
    exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Every point of a node box lies in the box of one of the node's leaves
(`rpre` is the reversed path prefix of the node). -/
theorem MTree.coverR : ∀ (T : MTree) (rpre : List ℕ) {a b t : ℝ},
    PtIn (boxOf rpre.reverse) a b t → ∃ q ∈ T.leavesR rpre, PtIn (boxOf q.1) a b t
  | .leaf l, rpre, a, b, t, h => ⟨(rpre.reverse, l), by simp [MTree.leavesR], h⟩
  | .node ax l r, rpre, a, b, t, h => by
      rcases ptIn_step h ax with h' | h'
      · rw [← boxOf_append, ← List.reverse_cons] at h'
        obtain ⟨q, hq, hq'⟩ := MTree.coverR l (2 * ax :: rpre) h'
        exact ⟨q, by simp only [MTree.leavesR, List.mem_append]; exact Or.inl hq, hq'⟩
      · rw [← boxOf_append, ← List.reverse_cons] at h'
        obtain ⟨q, hq, hq'⟩ := MTree.coverR r ((2 * ax + 1) :: rpre) h'
        exact ⟨q, by simp only [MTree.leavesR, List.mem_append]; exact Or.inr hq, hq'⟩

theorem MTree.cover (T : MTree) {a b t : ℝ} (h : PtIn (boxOf []) a b t) :
    ∃ q ∈ T.leaves, PtIn (boxOf q.1) a b t :=
  MTree.coverR T [] (by simpa using h)

/-- A point `(a, b, t)` of a box with `E = 11/200 + t (C0 - 11/200)` lies in the box image. -/
theorem inBox_of_ptIn {B : Box} {a b E t : ℝ} (h : PtIn B a b t)
    (hE : E = (E0 : ℝ) + t * ((H a + H b) / 2 - (E0 : ℝ)))
    (hC : (E0 : ℝ) ≤ (H a + H b) / 2) : InBox B a b E := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hC' : 0 ≤ (H a + H b) / 2 - (E0 : ℝ) := by linarith
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · rw [hE]; nlinarith [mul_le_mul_of_nonneg_right h5 hC']
  · rw [hE]; nlinarith [mul_le_mul_of_nonneg_right h6 hC']

/-- Coverage of the moderate-entropy domain by the leaves of the archived tree. -/
theorem modTree_cover {k : ℕ} (μ : InteriorLaw (Fin k))
    (ha0 : 1 / 10 ≤ μ.a) (ha1 : μ.a ≤ 1 / 2) (hb0 : 1 / 2 ≤ μ.b) (hb1 : μ.b ≤ 9 / 10)
    (hE : (E0 : ℝ) ≤ μ.meanEntropy) :
    ∃ q ∈ modTree.leaves, InBox (boxOf q.1) μ.a μ.b μ.meanEntropy := by
  have hEle : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_le_cap, μ.f_le_cap]
  set C := (H μ.a + H μ.b) / 2 with hCdef
  set t : ℝ := if (E0 : ℝ) < C then (μ.meanEntropy - E0) / (C - E0) else 0 with ht
  have htE : μ.meanEntropy = (E0 : ℝ) + t * (C - E0) := by
    rw [ht]
    split_ifs with hc
    · have hne : C - (E0 : ℝ) ≠ 0 := (sub_pos.mpr hc).ne'
      rw [div_mul_cancel₀ _ hne]
      ring
    · have : C = (E0 : ℝ) := by linarith
      rw [this]; ring_nf; linarith
  have ht01 : 0 ≤ t ∧ t ≤ 1 := by
    rw [ht]
    split_ifs with hc
    · constructor
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]; linarith
    · norm_num
  have hroot : PtIn (boxOf []) μ.a μ.b t := by
    simp only [boxOf, List.foldl_nil, boxRoot, PtIn]
    push_cast
    exact ⟨ha0, ha1, hb0, hb1, ht01.1, ht01.2⟩
  obtain ⟨q, hq, hq'⟩ := MTree.cover modTree hroot
  refine ⟨q, hq, inBox_of_ptIn hq' ?_ ?_⟩
  · rw [← hCdef]; exact htE
  · rw [← hCdef]; linarith

end CKLaneN1b

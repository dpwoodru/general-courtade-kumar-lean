import CKLaneG3.SliceBind
import CKLaneG3.SBind

/-!
# Lane G3b: per-chunk (subtree) binding lemmas for large (S) owner labels

The monolithic per-label walk over the whole 160,789-leaf `sTree` with a 59,175-entry certified list was
killed at 43 GB RSS (kernel).  Here the same per-label statement is assembled from per-chunk facts
(`CKLaneG3.fam_node` / `fam_root` along the `sTree` skeleton, `CKLaneG3.SBind`), each chunk walking only its
own subtree (≤ 4096 leaves) with only its own part of the certified list:

* `sub_family_of_range`  : a contiguous range `(L.drop a).take len` of a DFS-ordered certified list;
* `sub_family_of_slices` : a concatenation of shard slices (`CKLaneG3.sliceOf`).
Soundness depends on neither the range nor the runs (they only decide whether the kernel check succeeds).
-/

set_option autoImplicit false

universe u

namespace CKLaneG3

open CKLaneD

/-- Per-subtree binding from a contiguous range of a certified list. -/
theorem sub_family_of_range {Q : List ℕ → Prop} (T : PTree) (n : ℕ) (rpre : List ℕ) (L : List (List ℕ))
    (hL : ∀ p ∈ L, Q p) (a len : ℕ)
    (hc : (tconsume (fun l => l == n) T rpre ((L.drop a).take len)).isSome = true) :
    ∀ q ∈ T.leavesR rpre, q.2 = n → Q q.1 := by
  intro q hq hn
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp hc
  have hm := (tconsume_spec T rpre hL').1 q hq (by simp [hn])
  exact hL _ (List.mem_of_mem_drop (List.mem_of_mem_take hm))

/-- Per-subtree binding from a concatenation of shard slices. -/
theorem sub_family_of_slices {α : Type u} {Q : List ℕ → Prop} (T : PTree) (n : ℕ) (rpre : List ℕ)
    (SH : List (List α)) (f : α → List ℕ) (hSH : ∀ S ∈ SH, ∀ x ∈ S, Q (f x)) (runs : List (ℕ × ℕ × ℕ))
    (hc : (tconsume (fun l => l == n) T rpre (((runs.map (sliceOf SH)).flatten).map f)).isSome = true) :
    ∀ q ∈ T.leavesR rpre, q.2 = n → Q q.1 := by
  intro q hq hn
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp hc
  have hm := (tconsume_spec T rpre hL').1 q hq (by simp [hn])
  obtain ⟨x, hx, hxq⟩ := List.mem_map.mp hm
  obtain ⟨S, hS, hxS⟩ := mem_slices hx
  rw [← hxq]
  exact hSH S hS x hxS

end CKLaneG3

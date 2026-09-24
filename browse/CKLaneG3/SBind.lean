import CKLaneG3.PSort

/-!
# Lane G3: hierarchical (per-subtree) binding of certified path lists to tree leaves

The monolithic per-label binding (`label_family_of_psort` over the whole 160,789-leaf same-side tree)
costs ~13.5 GB of kernel memory per label.  Here the same statement is assembled from per-subtree
facts:

* `sub_family_of_filter` : for ANY subtree `T` (reversed path prefix `rpre`) and ANY prefix `pu`,
  the lane's certified list is filtered by `pfx pu`, merge-sorted (`psortM`, explicit merge fuel, no
  `length` recursion), and consumed by one DFS walk of `T` only.  Soundness does not depend on `pu`,
  `m` or `fuel` (they only affect whether the kernel check succeeds).
* `fam_node` / `fam_root` : subtree facts combine along the tree skeleton (`PTree.leavesR` of a node
  is the append of its children's lists).
-/

set_option autoImplicit false

namespace CKLaneG3

open CKLaneD

/-- Prefix test on paths (kernel friendly: `Nat.beq`). -/
def pfx : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => Nat.beq a b && pfx as bs

/-- Merge sort with explicit merge fuel `m` (no `List.length` in the kernel). -/
def psortM (m : ℕ) : ℕ → List (List ℕ) → List (List ℕ)
  | 0, l => l
  | n + 1, l =>
      match l with
      | [] => []
      | [x] => [x]
      | _ :: _ :: _ => pmerge m (psortM m n (psplit l).1) (psortM m n (psplit l).2)

theorem mem_psortM (m : ℕ) : ∀ (n : ℕ) (l : List (List ℕ)) (p : List ℕ), p ∈ psortM m n l ↔ p ∈ l
  | 0, l, p => by simp [psortM]
  | n + 1, [], p => by simp [psortM]
  | n + 1, [x], p => by simp [psortM]
  | n + 1, x :: y :: t, p => by
      simp only [psortM]
      rw [mem_pmerge, mem_psortM m n, mem_psortM m n]
      exact (mem_psplit (x :: y :: t) p).symm

/-- Per-subtree binding: the label-`n` leaves of the subtree `T` (reversed prefix `rpre`) satisfy
`Q`, given a certified list `L` (any order, any extra entries). -/
theorem sub_family_of_filter {Q : List ℕ → Prop} (T : PTree) (n : ℕ) (rpre pu : List ℕ)
    (m fuel : ℕ) (L : List (List ℕ)) (hL : ∀ p ∈ L, Q p)
    (hc : (tconsume (fun l => l == n) T rpre (psortM m fuel (L.filter (pfx pu)))).isSome = true) :
    ∀ q ∈ T.leavesR rpre, q.2 = n → Q q.1 := by
  intro q hq hn
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp hc
  have hm := (tconsume_spec T rpre hL').1 q hq (by simp [hn])
  rw [mem_psortM] at hm
  exact hL _ (List.mem_filter.mp hm).1

/-- A subtree without label-`n` leaves (one consumer walk with the empty list). -/
theorem sub_family_of_none {Q : List ℕ → Prop} (T : PTree) (n : ℕ) (rpre : List ℕ)
    (hc : (tconsume (fun l => l == n) T rpre []).isSome = true) :
    ∀ q ∈ T.leavesR rpre, q.2 = n → Q q.1 := by
  intro q hq hn
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp hc
  have hm := (tconsume_spec T rpre hL').1 q hq (by simp [hn])
  simp at hm

/-- Skeleton combination at a node. -/
theorem fam_node {P : List ℕ × ℕ → Prop} (ax : ℕ) (l r : PTree) (rpre : List ℕ)
    (hl : ∀ q ∈ l.leavesR (2 * ax :: rpre), P q)
    (hr : ∀ q ∈ r.leavesR ((2 * ax + 1) :: rpre), P q) :
    ∀ q ∈ (PTree.node ax l r).leavesR rpre, P q := by
  intro q hq
  simp only [PTree.leavesR, List.mem_append] at hq
  exact hq.elim (hl q) (hr q)

/-- Root: `leaves = leavesR []`. -/
theorem fam_root {P : List ℕ × ℕ → Prop} (T : PTree) (h : ∀ q ∈ T.leavesR [], P q) :
    ∀ q ∈ T.leaves, P q := h

end CKLaneG3

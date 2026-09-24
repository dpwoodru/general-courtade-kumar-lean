import CKLaneN6.FamBase

/-!
# Lane N6: tail-recursive path-list comparison for kernel decides

`pathsBeq` compares two lists of paths element by element with the recursive call in tail position, so
`decide +kernel` on `pathsBeq l1 l2 = true` runs iteratively in the kernel even for lists with thousands
of paths (`instDecidableEqList` nests the recursive call and exhausts the kernel stack there).
`pathsBeq_eq` turns a successful comparison into list equality.
-/

set_option autoImplicit false

namespace CKLaneN6

def pathsBeq : List (List ℕ) → List (List ℕ) → Bool
  | [], [] => true
  | a :: as, b :: bs => (a == b) && pathsBeq as bs
  | _, _ => false

theorem pathsBeq_eq : ∀ {l1 l2 : List (List ℕ)}, pathsBeq l1 l2 = true → l1 = l2
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [pathsBeq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, pathsBeq_eq h.2]
  | [], _ :: _, h => by simp [pathsBeq] at h
  | _ :: _, [], h => by simp [pathsBeq] at h

end CKLaneN6

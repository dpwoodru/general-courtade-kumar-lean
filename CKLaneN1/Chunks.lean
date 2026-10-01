import CKLaneN1.Tree

/-!
# Lane N1: chunked list checks

`all_of_chunks` assembles a whole-list Boolean check from fixed-length chunk checks (one fleet
shard per chunk), so the aggregators never re-evaluate the leaf checks.
-/

namespace CKLaneN1

/-- A list satisfies `f` everywhere if each of its `m` chunks of length `N` does. -/
theorem all_of_chunks {α : Type} (f : α → Bool) (N : ℕ) :
    ∀ (m : ℕ) (l : List α), l.length ≤ N * m →
      (∀ k < m, ((l.drop (N * k)).take N).all f = true) → l.all f = true
  | 0, l, hlen, _ => by
      have hl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      simp [hl]
  | m + 1, l, hlen, h => by
      have h0 := h 0 (Nat.succ_pos m)
      simp only [Nat.mul_zero, List.drop_zero] at h0
      have hrest : (l.drop N).all f = true := by
        apply all_of_chunks f N m (l.drop N)
        · simp only [List.length_drop]
          rw [Nat.mul_succ] at hlen
          omega
        · intro k hk
          have hk' := h (k + 1) (by omega)
          rw [List.drop_drop]
          rw [show N + N * k = N * (k + 1) by ring]
          exact hk'
      rw [← List.take_append_drop N l, List.all_append, h0, hrest]
      rfl

end CKLaneN1

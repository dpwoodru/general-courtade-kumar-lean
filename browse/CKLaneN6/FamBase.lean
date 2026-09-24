import CKLaneN6.Check

/-! Lane N6: list helper for the family modules. -/

set_option autoImplicit false

namespace CKLaneN6

theorem forall_mem_append' {α : Type} {P : α → Prop} {l1 l2 : List α}
    (h1 : ∀ q ∈ l1, P q) (h2 : ∀ q ∈ l2, P q) : ∀ q ∈ l1 ++ l2, P q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact h1 q h
  · exact h2 q h

end CKLaneN6

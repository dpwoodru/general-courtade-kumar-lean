import CKLaneC.S3.SlopeChain

set_option autoImplicit false

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain

namespace CKLaneC.SAxis.Data

theorem forall_mem_cons_of {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a)
    (hl : ∀ x ∈ l, P x) : ∀ x ∈ a :: l, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | h
  · exact ha
  · exact hl x h

theorem forall_mem_nil_of {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by
  intro x hx
  simp at hx

theorem forall_mem_append_of {α : Type} {P : α → Prop} {A B : List α} (hA : ∀ x ∈ A, P x)
    (hB : ∀ x ∈ B, P x) : ∀ x ∈ A ++ B, P x := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hA x h
  · exact hB x h

theorem tableValid_nil : TableValid [] := by
  intro c hc
  simp at hc

theorem tableValid_cons {c : List Piece} {T : List (List Piece)}
    (hc : ∀ p ∈ c, p.check = true) (hT : TableValid T) : TableValid (c :: T) := by
  intro c' hc' p hp
  rcases List.mem_cons.mp hc' with rfl | h
  · exact hc p hp
  · exact hT c' h p hp

end CKLaneC.SAxis.Data

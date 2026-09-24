import CKLaneN1.R3Leaf

/-!
# Lane M07 / CE-stat row 3: gluing lemmas for the numeric cover

`sem_node`: `Sem` of the two halves of a box along any axis gives `Sem` of the box (N1 `B3.mem_step`);
`sem_eq`: transport along an equality of boxes (used with `decide` to match a generated sub-root literal).
The octave modules compose these along the generated skeleton, so the proof term has the depth of the
skeleton, not the number of shards.
-/

set_option autoImplicit false

namespace CKLaneM07.CE.R3Glue

open CKLaneN1

theorem sem_node {B : B3} (ax : ℕ) (h0 : CKLaneN1.R3.Sem (B.step (2 * ax)))
    (h1 : CKLaneN1.R3.Sem (B.step (2 * ax + 1))) : CKLaneN1.R3.Sem B := by
  intro a z y hm
  rcases B3.mem_step hm ax with h | h
  · exact h0 a z y h
  · exact h1 a z y h

theorem sem_eq {B B' : B3} (h : B = B') (s : CKLaneN1.R3.Sem B') : CKLaneN1.R3.Sem B := h ▸ s

end CKLaneM07.CE.R3Glue

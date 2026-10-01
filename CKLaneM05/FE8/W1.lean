import CKLaneM05.FE8.Parent

/-!
# Lane M05 / FE8: certificate type v1 (outside, cap, parent) and shard-entry soundness

`W1.check_sound : W1.check B w = true → LeafOK B`. A shard is a list of archived paths with
certificate trees below their boxes (`CT W1`, refinement inside a leaf allowed); `entries_sound`
turns one kernel-evaluated `List.all` into `∀ q ∈ paths, LeafOK (feBox q)`. The facts produced are
independent of the certificate type, so later kernels (new certificate types) add facts without
invalidating earlier shards.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05.FE8

/-- FE8 certificate, version 1. -/
inductive W1 where
  | outside
  | cap
  | parent (w : PW)
  deriving Repr

def W1.check (B : CKLaneD.Box) : W1 → Bool
  | .outside => decide (B.bhi - B.alo < 1 / 20)
  | .cap => capCheck B
  | .parent w => parentCheck B w

theorem W1.check_sound : ∀ (B : CKLaneD.Box) (w : W1), W1.check B w = true → LeafOK B
  | _, .outside, h => leafOK_of_outside (by simpa [W1.check] using h)
  | _, .cap, h => leafOK_of_cap h
  | _, .parent _, h => leafOK_of_parentCheck h

/-- A shard: archived paths with certificate trees; one Boolean check for all of them. -/
theorem entries_sound {α : Type} (chk : CKLaneD.Box → α → Bool)
    (hchk : ∀ B w, chk B w = true → LeafOK B) (L : List (List ℕ × CT α))
    (h : L.all (fun x => x.2.check chk (feBox x.1)) = true) :
    ∀ q ∈ L.map Prod.fst, LeafOK (feBox q) := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
  rw [List.all_eq_true] at h
  exact CT.sound chk hchk x.2 _ (h x hx)

end CKLaneM05.FE8

#check @CKLaneM05.FE8.W1.check_sound
#check @CKLaneM05.FE8.entries_sound
#print axioms CKLaneM05.FE8.W1.check_sound
#print axioms CKLaneM05.FE8.entries_sound

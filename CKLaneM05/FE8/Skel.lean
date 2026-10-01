import CKLaneM05.FE8.Base

/-!
# Lane M05 / FE8: skeleton of the archived tree above the shard subtrees

The archived FULL_ENTROPY (8) partition is a binary tree of exact halvings of `feRoot`. Shards prove
`LeafOK (feBox p)` for subtree roots `p` (certificate trees `CT` that follow the archived splits and
refine inside archived leaves). The skeleton `Sk` is the part of the archived tree above those
roots: `Sk.sound` combines the subtree facts by `leafOK_split`, and `root_of_skel` gives
`LeafOK feRoot` once every skeleton leaf path is covered by a shard fact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05.FE8

/-- Upper part of the archived tree; its leaves are the subtree roots proved by shards. -/
inductive Sk where
  | leaf
  | node (ax : ℕ) (l r : Sk)
  deriving Repr

/-- Leaf paths of a skeleton below the path `p`, left to right. -/
def Sk.leaves : Sk → List ℕ → List (List ℕ)
  | Sk.leaf, p => [p]
  | Sk.node ax l r, p => l.leaves (p ++ [2 * ax]) ++ r.leaves (p ++ [2 * ax + 1])

/-- All split axes are `a`, `b` or `t`. -/
def Sk.axOK : Sk → Bool
  | Sk.leaf => true
  | Sk.node ax l r => decide (ax < 3) && l.axOK && r.axOK

theorem Sk.sound : ∀ (T : Sk) (p : List ℕ), T.axOK = true →
    (∀ q ∈ T.leaves p, LeafOK (feBox q)) → LeafOK (feBox p)
  | Sk.leaf, p, _, h => h p (by simp [Sk.leaves])
  | Sk.node ax l r, p, hax, h => by
      simp only [Sk.axOK, Bool.and_eq_true, decide_eq_true_eq] at hax
      obtain ⟨⟨hax, hl⟩, hr⟩ := hax
      have h0 := Sk.sound l (p ++ [2 * ax]) hl (fun q hq => h q (by simp [Sk.leaves, hq]))
      have h1 := Sk.sound r (p ++ [2 * ax + 1]) hr (fun q hq => h q (by simp [Sk.leaves, hq]))
      exact leafOK_split p _ _ ax hax rfl rfl h0 h1

/-- The whole archived box from a skeleton whose leaves are all covered. -/
theorem root_of_skel (T : Sk) (L : List (List ℕ)) (hL : T.leaves [] = L) (hax : T.axOK = true)
    (h : ∀ q ∈ L, LeafOK (feBox q)) : LeafOK feRoot := by
  have := Sk.sound T [] hax (by rw [hL]; exact h)
  simpa [feBox] using this

/-- Covering facts for a concatenation of shard root lists. -/
theorem facts_append {L1 L2 : List (List ℕ)} (h1 : ∀ q ∈ L1, LeafOK (feBox q))
    (h2 : ∀ q ∈ L2, LeafOK (feBox q)) : ∀ q ∈ L1 ++ L2, LeafOK (feBox q) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact h1 q hq
  · exact h2 q hq

end CKLaneM05.FE8

#check @CKLaneM05.FE8.Sk.sound
#check @CKLaneM05.FE8.root_of_skel
#print axioms CKLaneM05.FE8.Sk.sound
#print axioms CKLaneM05.FE8.root_of_skel
#print axioms CKLaneM05.FE8.facts_append

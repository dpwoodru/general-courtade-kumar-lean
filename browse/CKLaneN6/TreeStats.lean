import CKLaneN6.TreeBase

/-!
# Lane N6: structural statistics of partition trees

`numLeaves`, `countLabel` are computed by structural recursion without building paths, and agree with
the leaf list: `leaves_length`, `leaves_countLabel`.  They make leaf/label counts of the 76,547-leaf archived
tree cheap to certify by `decide +kernel`.
-/

set_option autoImplicit false

namespace CKLaneN6

def PTree.numLeaves : PTree → ℕ
  | .leaf _ => 1
  | .node _ l r => l.numLeaves + r.numLeaves

def PTree.countLabel (c : ℕ) : PTree → ℕ
  | .leaf l => if l = c then 1 else 0
  | .node _ l r => l.countLabel c + r.countLabel c

theorem PTree.leavesR_length : ∀ (T : PTree) (rpre : List ℕ), (T.leavesR rpre).length = T.numLeaves
  | .leaf _, _ => rfl
  | .node ax l r, rpre => by
      simp only [PTree.leavesR, PTree.numLeaves, List.length_append, PTree.leavesR_length l,
        PTree.leavesR_length r]

theorem PTree.leaves_length (T : PTree) : T.leaves.length = T.numLeaves := T.leavesR_length []

theorem PTree.leavesR_countLabel (c : ℕ) : ∀ (T : PTree) (rpre : List ℕ),
    ((T.leavesR rpre).filter (fun x => x.2 = c)).length = T.countLabel c
  | .leaf l, _ => by
      by_cases h : l = c
      · simp [PTree.leavesR, PTree.countLabel, h]
      · simp [PTree.leavesR, PTree.countLabel, h]
  | .node ax l r, rpre => by
      simp only [PTree.leavesR, PTree.countLabel, List.filter_append, List.length_append,
        PTree.leavesR_countLabel c l, PTree.leavesR_countLabel c r]

theorem PTree.leaves_countLabel (T : PTree) (c : ℕ) :
    (T.leaves.filter (fun x => x.2 = c)).length = T.countLabel c := T.leavesR_countLabel c []

end CKLaneN6

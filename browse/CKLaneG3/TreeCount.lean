import CKLaneG3.Families

/-!
# Lane G3: label-only leaf counting on `PTree` (cheap kernel walks)

`tcount T = (T.leavesR rpre).length` and
`tcountLabel n T = ((T.leavesR rpre).filter (fun q => q.2 = n)).length`, so leaf / label counts of
large literal trees are decided by `decide +kernel` on a walk that builds no lists.
-/

namespace CKLaneG3

open CKLaneD

/-- Number of leaves. -/
def tcount : PTree → ℕ
  | .leaf _ => 1
  | .node _ l r => tcount l + tcount r

/-- Number of leaves with owner label `n`. -/
def tcountLabel (n : ℕ) : PTree → ℕ
  | .leaf l => if l = n then 1 else 0
  | .node _ l r => tcountLabel n l + tcountLabel n r

theorem tcount_eq : ∀ (T : PTree) (rpre : List ℕ), tcount T = (T.leavesR rpre).length
  | .leaf _, _ => by simp [tcount, PTree.leavesR]
  | .node ax l r, rpre => by
      simp only [tcount, PTree.leavesR, List.length_append]
      rw [tcount_eq l (2 * ax :: rpre), tcount_eq r ((2 * ax + 1) :: rpre)]

theorem tcountLabel_eq (n : ℕ) : ∀ (T : PTree) (rpre : List ℕ),
    tcountLabel n T = ((T.leavesR rpre).filter (fun q => q.2 = n)).length
  | .leaf l, _ => by
      by_cases h : l = n
      · simp [tcountLabel, PTree.leavesR, h]
      · simp [tcountLabel, PTree.leavesR, h]
  | .node ax l r, rpre => by
      simp only [tcountLabel, PTree.leavesR, List.filter_append, List.length_append]
      rw [tcountLabel_eq n l (2 * ax :: rpre), tcountLabel_eq n r ((2 * ax + 1) :: rpre)]

end CKLaneG3

import CKLaneN6.Tree

/-!
# Lane N6: coverage of the Thm 3 row by the archived partition tree

`archTree_cover`: every interior law with `a ≤ b`, `1/10 ≤ a`, `b ≤ 1/2`, `10^-6 ≤ E` (in particular every
law of `CKLaneN23.SmallRatioT3NearRest`) lies in the exact box `CKLaneM05.FE8.feBox q.1` of some leaf `q`
(any label) of the archived tree.  `row_of_all_leaves`: the Thm 3 obligation on every leaf gives the row.
-/

set_option autoImplicit false

namespace CKLaneN6

open GeneralCK CKLaneM05.FE8 CKLaneN6.ArchTree

theorem archTree_wf : archTree.wf = true := by decide +kernel

theorem archTree_cover {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b) (ha : 1 / 10 ≤ μ.a)
    (hb : μ.b ≤ 1 / 2) (hE : 1 / 1000000 ≤ μ.meanEntropy) :
    ∃ q ∈ archTree.leaves, CKLaneD.InBox (feBox q.1) μ.a μ.b μ.meanEntropy :=
  PTree.cover archTree archTree_wf (inBox_feRoot μ hab ha hb hE)

theorem row_of_all_leaves (h : ∀ q ∈ archTree.leaves, LeafOK (feBox q.1)) :
    CKLaneN23.SmallRatioT3NearRest :=
  PTree.row_of_leaves archTree archTree_wf h

end CKLaneN6

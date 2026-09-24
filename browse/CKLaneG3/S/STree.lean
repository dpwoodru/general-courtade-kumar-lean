import CKLaneG3.TreeCount
import CKLaneG3.S.Chunk.C_4
import CKLaneG3.S.Chunk.C_50202020204
import CKLaneG3.S.Chunk.C_50202020205
import CKLaneG3.S.Chunk.C_5020202021
import CKLaneG3.S.Chunk.C_502020203040
import CKLaneG3.S.Chunk.C_5020202030414
import CKLaneG3.S.Chunk.C_5020202030415
import CKLaneG3.S.Chunk.C_50202020305
import CKLaneG3.S.Chunk.C_50202020314
import CKLaneG3.S.ChunkG.G_50202020315
import CKLaneG3.S.Chunk.C_50202021
import CKLaneG3.S.Chunk.C_502020300420
import CKLaneG3.S.Chunk.C_5020203004214
import CKLaneG3.S.Chunk.C_50202030042152
import CKLaneG3.S.Chunk.C_50202030042153
import CKLaneG3.S.Chunk.C_502020300430
import CKLaneG3.S.Chunk.C_5020203004314
import CKLaneG3.S.Chunk.C_50202030043150
import CKLaneG3.S.Chunk.C_502020300431512
import CKLaneG3.S.Chunk.C_502020300431513
import CKLaneG3.S.Chunk.C_50202030052
import CKLaneG3.S.Chunk.C_50202030053
import CKLaneG3.S.Chunk.C_50202030142
import CKLaneG3.S.Chunk.C_50202030143
import CKLaneG3.S.Chunk.C_5020203015
import CKLaneG3.S.Chunk.C_50202031
import CKLaneG3.S.Chunk.C_502021
import CKLaneG3.S.Chunk.C_50203000
import CKLaneG3.S.Chunk.C_50203001420
import CKLaneG3.S.Chunk.C_50203001421
import CKLaneG3.S.Chunk.C_50203001430
import CKLaneG3.S.Chunk.C_50203001431
import CKLaneG3.S.Chunk.C_5020300152
import CKLaneG3.S.Chunk.C_50203001530
import CKLaneG3.S.Chunk.C_50203001531
import CKLaneG3.S.Chunk.C_5020301
import CKLaneG3.S.Chunk.C_502031
import CKLaneG3.S.Chunk.C_5021
import CKLaneG3.S.Chunk.C_5030000
import CKLaneG3.S.Chunk.C_50300014
import CKLaneG3.S.Chunk.C_5030001520
import CKLaneG3.S.Chunk.C_50300015212402
import CKLaneG3.S.Chunk.C_50300015212403
import CKLaneG3.S.Chunk.C_50300015212412
import CKLaneG3.S.Chunk.C_50300015212413
import CKLaneG3.S.Chunk.C_503000152125
import CKLaneG3.S.Chunk.C_5030001521340
import CKLaneG3.S.Chunk.C_503000152134124
import CKLaneG3.S.Chunk.C_503000152134125
import CKLaneG3.S.Chunk.C_50300015213413
import CKLaneG3.S.Chunk.C_503000152135
import CKLaneG3.S.Chunk.C_503000153
import CKLaneG3.S.Chunk.C_5030010420
import CKLaneG3.S.Chunk.C_5030010421
import CKLaneG3.S.Chunk.C_503001043
import CKLaneG3.S.ChunkG.G_503001053042052
import CKLaneG3.S.ChunkG.G_5030010530431531
import CKLaneG3.S.ChunkG.G_503001143

/-!
# Lane G3: the canonical same-side (S) tree (BRIEF §7)

All 160789 leaves of `same_side/ADAPT_RESULT.json` (sha256 b134020b83227cdfb54ec8a85cebf00a67bc2537320b0731836fbc8f324fe9c8) with owner labels
0 = normalized_logsum, 1 = mean_logsum, 2 = endpoint, 3 = entropy_endpoints, 4 = derivative, 5 = central, 6 = small_mean, 7 = parent, 8 = parent_tail.
A node `N ax l r` halves axis `ax` (0 = x, 1 = b, 2 = t) at its midpoint; `l` is the lower half
(digit `2 ax`), `r` the upper half (digit `2 ax + 1`), exactly as `COVER.reconstruct`.
Assembled from 83 chunk modules (maximal subtrees with <= 4096 leaves).
-/

namespace CKLaneG3.S

open CKLaneD CKLaneG3

local notation "N" => PTree.node

set_option maxRecDepth 100000 in
/-- The archived same-side cover as a labelled halving tree. -/
def sTree : PTree :=
  (N 2 CKLaneG3.S.Chunk.C_4.t (N 0 (N 1 (N 0 (N 1 (N 0 (N 1 (N 0 (N 1 (N 0 (N 2 CKLaneG3.S.Chunk.C_50202020204.t CKLaneG3.S.Chunk.C_50202020205.t) CKLaneG3.S.Chunk.C_5020202021.t) (N 0 (N 2 (N 0 CKLaneG3.S.Chunk.C_502020203040.t (N 2 CKLaneG3.S.Chunk.C_5020202030414.t CKLaneG3.S.Chunk.C_5020202030415.t)) CKLaneG3.S.Chunk.C_50202020305.t) (N 2 CKLaneG3.S.Chunk.C_50202020314.t CKLaneG3.S.Chunk.C_50202020315.t))) CKLaneG3.S.Chunk.C_50202021.t) (N 0 (N 0 (N 2 (N 1 (N 0 CKLaneG3.S.Chunk.C_502020300420.t (N 2 CKLaneG3.S.Chunk.C_5020203004214.t (N 1 CKLaneG3.S.Chunk.C_50202030042152.t CKLaneG3.S.Chunk.C_50202030042153.t))) (N 0 CKLaneG3.S.Chunk.C_502020300430.t (N 2 CKLaneG3.S.Chunk.C_5020203004314.t (N 0 CKLaneG3.S.Chunk.C_50202030043150.t (N 1 CKLaneG3.S.Chunk.C_502020300431512.t CKLaneG3.S.Chunk.C_502020300431513.t))))) (N 1 CKLaneG3.S.Chunk.C_50202030052.t CKLaneG3.S.Chunk.C_50202030053.t)) (N 2 (N 1 CKLaneG3.S.Chunk.C_50202030142.t CKLaneG3.S.Chunk.C_50202030143.t) CKLaneG3.S.Chunk.C_5020203015.t)) CKLaneG3.S.Chunk.C_50202031.t)) CKLaneG3.S.Chunk.C_502021.t) (N 0 (N 0 (N 0 CKLaneG3.S.Chunk.C_50203000.t (N 2 (N 1 (N 0 CKLaneG3.S.Chunk.C_50203001420.t CKLaneG3.S.Chunk.C_50203001421.t) (N 0 CKLaneG3.S.Chunk.C_50203001430.t CKLaneG3.S.Chunk.C_50203001431.t)) (N 1 CKLaneG3.S.Chunk.C_5020300152.t (N 0 CKLaneG3.S.Chunk.C_50203001530.t CKLaneG3.S.Chunk.C_50203001531.t)))) CKLaneG3.S.Chunk.C_5020301.t) CKLaneG3.S.Chunk.C_502031.t)) CKLaneG3.S.Chunk.C_5021.t) (N 0 (N 0 (N 0 (N 0 CKLaneG3.S.Chunk.C_5030000.t (N 2 CKLaneG3.S.Chunk.C_50300014.t (N 1 (N 0 CKLaneG3.S.Chunk.C_5030001520.t (N 1 (N 2 (N 0 (N 1 CKLaneG3.S.Chunk.C_50300015212402.t CKLaneG3.S.Chunk.C_50300015212403.t) (N 1 CKLaneG3.S.Chunk.C_50300015212412.t CKLaneG3.S.Chunk.C_50300015212413.t)) CKLaneG3.S.Chunk.C_503000152125.t) (N 2 (N 0 CKLaneG3.S.Chunk.C_5030001521340.t (N 1 (N 2 CKLaneG3.S.Chunk.C_503000152134124.t CKLaneG3.S.Chunk.C_503000152134125.t) CKLaneG3.S.Chunk.C_50300015213413.t)) CKLaneG3.S.Chunk.C_503000152135.t))) CKLaneG3.S.Chunk.C_503000153.t))) (N 0 (N 2 (N 1 (N 0 CKLaneG3.S.Chunk.C_5030010420.t CKLaneG3.S.Chunk.C_5030010421.t) CKLaneG3.S.Chunk.C_503001043.t) (N 1 (N 0 (N 1 CKLaneG3.S.Chunk.C_50300105202.t (N 2 (N 0 (N 1 CKLaneG3.S.Chunk.C_50300105203402.t CKLaneG3.S.Chunk.C_50300105203403.t) CKLaneG3.S.Chunk.C_5030010520341.t) CKLaneG3.S.Chunk.C_503001052035.t)) CKLaneG3.S.Chunk.C_5030010521.t) (N 0 (N 2 (N 1 (N 0 (N 2 CKLaneG3.S.Chunk.C_50300105304204.t (N 1 CKLaneG3.S.Chunk.C_503001053042052.t CKLaneG3.S.Chunk.C_503001053042053.t)) (N 2 CKLaneG3.S.Chunk.C_50300105304214.t CKLaneG3.S.Chunk.C_50300105304215.t)) (N 0 CKLaneG3.S.Chunk.C_5030010530430.t (N 2 CKLaneG3.S.Chunk.C_50300105304314.t (N 1 CKLaneG3.S.Chunk.C_503001053043152.t (N 0 CKLaneG3.S.Chunk.C_5030010530431530.t CKLaneG3.S.Chunk.C_5030010530431531.t))))) CKLaneG3.S.Chunk.C_50300105305.t) (N 2 (N 1 CKLaneG3.S.Chunk.C_503001053142.t (N 0 (N 2 CKLaneG3.S.Chunk.C_50300105314304.t CKLaneG3.S.Chunk.C_50300105314305.t) CKLaneG3.S.Chunk.C_5030010531431.t)) CKLaneG3.S.Chunk.C_50300105315.t)))) (N 2 (N 1 CKLaneG3.S.Chunk.C_503001142.t CKLaneG3.S.Chunk.C_503001143.t) CKLaneG3.S.Chunk.C_50300115.t))) CKLaneG3.S.Chunk.C_50301.t) CKLaneG3.S.Chunk.C_5031.t)) CKLaneG3.S.Chunk.C_51.t))

theorem sTree_leaf_count : sTree.leaves.length = 160789 := by
  rw [PTree.leaves, ← tcount_eq]
  decide +kernel

/-- owner label 0 = `normalized_logsum`. -/
theorem sTree_label0_count : (sTree.leaves.filter (fun q => q.2 = 0)).length = 59175 := by
  rw [PTree.leaves, ← tcountLabel_eq]
  decide +kernel

/-- owner label 1 = `mean_logsum`. -/
theorem sTree_label1_count : (sTree.leaves.filter (fun q => q.2 = 1)).length = 50429 := by
  rw [PTree.leaves, ← tcountLabel_eq]
  decide +kernel

/-- owner label 2 = `endpoint`. -/
theorem sTree_label2_count : (sTree.leaves.filter (fun q => q.2 = 2)).length = 37506 := by
  rw [PTree.leaves, ← tcountLabel_eq]
  decide +kernel

/-- owner label 3 = `entropy_endpoints`. -/
theorem sTree_label3_count : (sTree.leaves.filter (fun q => q.2 = 3)).length = 7657 := by
  rw [PTree.leaves, ← tcountLabel_eq]
  decide +kernel

/-- owner label 4 = `derivative`. -/
theorem sTree_label4_count : (sTree.leaves.filter (fun q => q.2 = 4)).length = 3205 := by
  rw [PTree.leaves, ← tcountLabel_eq]
  decide +kernel

/-- owner label 5 = `central`. -/
theorem sTree_label5_count : (sTree.leaves.filter (fun q => q.2 = 5)).length = 2458 := by
  rw [PTree.leaves, ← tcountLabel_eq]
  decide +kernel

/-- owner label 6 = `small_mean`. -/
theorem sTree_label6_count : (sTree.leaves.filter (fun q => q.2 = 6)).length = 266 := by
  rw [PTree.leaves, ← tcountLabel_eq]
  decide +kernel

/-- owner label 7 = `parent`. -/
theorem sTree_label7_count : (sTree.leaves.filter (fun q => q.2 = 7)).length = 69 := by
  rw [PTree.leaves, ← tcountLabel_eq]
  decide +kernel

/-- owner label 8 = `parent_tail`. -/
theorem sTree_label8_count : (sTree.leaves.filter (fun q => q.2 = 8)).length = 24 := by
  rw [PTree.leaves, ← tcountLabel_eq]
  decide +kernel

/-- Every owner label is < 9 (label-only walk). -/
theorem sTree_labels_lt9 : tallLabels (fun l => decide (l < 9)) sTree = true := by
  decide +kernel

end CKLaneG3.S

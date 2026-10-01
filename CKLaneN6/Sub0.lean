import CKLaneN6.Tree
import CKLaneN6.AsmBase
import CKLaneN6.Cs.C0000
import CKLaneN6.Cs.C0001
import CKLaneN6.Cs.C0002
import CKLaneN6.Cs.C0003
import CKLaneN6.Cs.C0004
import CKLaneN6.Cs.C0005
import CKLaneN6.Cs.C0006
import CKLaneN6.Cs.C0007
import CKLaneN6.Cs.C0008
import CKLaneN6.Cs.C0009
import CKLaneN6.Cs.C0010
import CKLaneN6.Cs.C0011
import CKLaneN6.Cs.C0012
import CKLaneN6.Cs.C0013
import CKLaneN6.Cs.C0014
import CKLaneN6.Cs.C0015

/-! Lane N6 assembly part 0: depth-6 subtrees 024024..025135 of the archived tree, each
matched (kernel decide over the overlapping coarse shards only) with the shard leaf lists. -/

set_option autoImplicit false

namespace CKLaneN6.Asm

open CKLaneN6 CKLaneM05.FE8

set_option maxHeartbeats 0 in
/-- Subtree `024024`: 2163 archived leaves (DFS range 0..2162). -/
theorem sub_024024 : (ArchTree.t024024.leavesR [4, 2, 0, 4, 2, 0]).map Prod.fst =
    ((Cs.C0000.paths).drop 0).take 2163 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_024024 : ∀ q ∈ ArchTree.t024024.leavesR [4, 2, 0, 4, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0000.paths).drop 0).take 2163 := by
    rw [← sub_024024]; exact List.mem_map_of_mem hq
  exact Cs.C0000.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `024025`: 6292 archived leaves (DFS range 2163..8454). -/
theorem sub_024025 : (ArchTree.t024025.leavesR [5, 2, 0, 4, 2, 0]).map Prod.fst =
    ((Cs.C0000.paths ++ Cs.C0001.paths).drop 2163).take 6292 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_024025 : ∀ q ∈ ArchTree.t024025.leavesR [5, 2, 0, 4, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0000.paths ++ Cs.C0001.paths).drop 2163).take 6292 := by
    rw [← sub_024025]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0000.leafOK Cs.C0001.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `024034`: 734 archived leaves (DFS range 8455..9188). -/
theorem sub_024034 : (ArchTree.t024034.leavesR [4, 3, 0, 4, 2, 0]).map Prod.fst =
    ((Cs.C0001.paths ++ Cs.C0002.paths).drop 3956).take 734 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_024034 : ∀ q ∈ ArchTree.t024034.leavesR [4, 3, 0, 4, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0001.paths ++ Cs.C0002.paths).drop 3956).take 734 := by
    rw [← sub_024034]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0001.leafOK Cs.C0002.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `024035`: 5266 archived leaves (DFS range 9189..14454). -/
theorem sub_024035 : (ArchTree.t024035.leavesR [5, 3, 0, 4, 2, 0]).map Prod.fst =
    ((Cs.C0002.paths ++ Cs.C0003.paths).drop 620).take 5266 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_024035 : ∀ q ∈ ArchTree.t024035.leavesR [5, 3, 0, 4, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0002.paths ++ Cs.C0003.paths).drop 620).take 5266 := by
    rw [← sub_024035]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0002.leafOK Cs.C0003.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `024124`: 1 archived leaves (DFS range 14455..14455). -/
theorem sub_024124 : (ArchTree.t024124.leavesR [4, 2, 1, 4, 2, 0]).map Prod.fst =
    ((Cs.C0003.paths).drop 1537).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_024124 : ∀ q ∈ ArchTree.t024124.leavesR [4, 2, 1, 4, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0003.paths).drop 1537).take 1 := by
    rw [← sub_024124]; exact List.mem_map_of_mem hq
  exact Cs.C0003.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `024125`: 1 archived leaves (DFS range 14456..14456). -/
theorem sub_024125 : (ArchTree.t024125.leavesR [5, 2, 1, 4, 2, 0]).map Prod.fst =
    ((Cs.C0003.paths).drop 1538).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_024125 : ∀ q ∈ ArchTree.t024125.leavesR [5, 2, 1, 4, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0003.paths).drop 1538).take 1 := by
    rw [← sub_024125]; exact List.mem_map_of_mem hq
  exact Cs.C0003.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `024134`: 2783 archived leaves (DFS range 14457..17239). -/
theorem sub_024134 : (ArchTree.t024134.leavesR [4, 3, 1, 4, 2, 0]).map Prod.fst =
    ((Cs.C0003.paths).drop 1539).take 2783 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_024134 : ∀ q ∈ ArchTree.t024134.leavesR [4, 3, 1, 4, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0003.paths).drop 1539).take 2783 := by
    rw [← sub_024134]; exact List.mem_map_of_mem hq
  exact Cs.C0003.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `024135`: 6789 archived leaves (DFS range 17240..24028). -/
theorem sub_024135 : (ArchTree.t024135.leavesR [5, 3, 1, 4, 2, 0]).map Prod.fst =
    ((Cs.C0004.paths ++ Cs.C0005.paths).drop 0).take 6789 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_024135 : ∀ q ∈ ArchTree.t024135.leavesR [5, 3, 1, 4, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0004.paths ++ Cs.C0005.paths).drop 0).take 6789 := by
    rw [← sub_024135]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0004.leafOK Cs.C0005.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `025024`: 6246 archived leaves (DFS range 24029..30274). -/
theorem sub_025024 : (ArchTree.t025024.leavesR [4, 2, 0, 5, 2, 0]).map Prod.fst =
    ((Cs.C0005.paths ++ Cs.C0006.paths).drop 804).take 6246 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_025024 : ∀ q ∈ ArchTree.t025024.leavesR [4, 2, 0, 5, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0005.paths ++ Cs.C0006.paths).drop 804).take 6246 := by
    rw [← sub_025024]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0005.leafOK Cs.C0006.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `025025`: 3073 archived leaves (DFS range 30275..33347). -/
theorem sub_025025 : (ArchTree.t025025.leavesR [5, 2, 0, 5, 2, 0]).map Prod.fst =
    ((Cs.C0006.paths ++ Cs.C0007.paths ++ Cs.C0008.paths ++ Cs.C0009.paths ++ Cs.C0010.paths ++ Cs.C0011.paths).drop 2487).take 3073 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_025025 : ∀ q ∈ ArchTree.t025025.leavesR [5, 2, 0, 5, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0006.paths ++ Cs.C0007.paths ++ Cs.C0008.paths ++ Cs.C0009.paths ++ Cs.C0010.paths ++ Cs.C0011.paths).drop 2487).take 3073 := by
    rw [← sub_025025]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' Cs.C0006.leafOK Cs.C0007.leafOK) Cs.C0008.leafOK) Cs.C0009.leafOK) Cs.C0010.leafOK) Cs.C0011.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `025034`: 4285 archived leaves (DFS range 33348..37632). -/
theorem sub_025034 : (ArchTree.t025034.leavesR [4, 3, 0, 5, 2, 0]).map Prod.fst =
    ((Cs.C0011.paths ++ Cs.C0012.paths).drop 492).take 4285 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_025034 : ∀ q ∈ ArchTree.t025034.leavesR [4, 3, 0, 5, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0011.paths ++ Cs.C0012.paths).drop 492).take 4285 := by
    rw [← sub_025034]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0011.leafOK Cs.C0012.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `025035`: 671 archived leaves (DFS range 37633..38303). -/
theorem sub_025035 : (ArchTree.t025035.leavesR [5, 3, 0, 5, 2, 0]).map Prod.fst =
    ((Cs.C0012.paths ++ Cs.C0013.paths).drop 331).take 671 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_025035 : ∀ q ∈ ArchTree.t025035.leavesR [5, 3, 0, 5, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0012.paths ++ Cs.C0013.paths).drop 331).take 671 := by
    rw [← sub_025035]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0012.leafOK Cs.C0013.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `025124`: 1 archived leaves (DFS range 38304..38304). -/
theorem sub_025124 : (ArchTree.t025124.leavesR [4, 2, 1, 5, 2, 0]).map Prod.fst =
    ((Cs.C0013.paths).drop 299).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_025124 : ∀ q ∈ ArchTree.t025124.leavesR [4, 2, 1, 5, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0013.paths).drop 299).take 1 := by
    rw [← sub_025124]; exact List.mem_map_of_mem hq
  exact Cs.C0013.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `025125`: 1 archived leaves (DFS range 38305..38305). -/
theorem sub_025125 : (ArchTree.t025125.leavesR [5, 2, 1, 5, 2, 0]).map Prod.fst =
    ((Cs.C0013.paths).drop 300).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_025125 : ∀ q ∈ ArchTree.t025125.leavesR [5, 2, 1, 5, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0013.paths).drop 300).take 1 := by
    rw [← sub_025125]; exact List.mem_map_of_mem hq
  exact Cs.C0013.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `025134`: 3909 archived leaves (DFS range 38306..42214). -/
theorem sub_025134 : (ArchTree.t025134.leavesR [4, 3, 1, 5, 2, 0]).map Prod.fst =
    ((Cs.C0013.paths ++ Cs.C0014.paths).drop 301).take 3909 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_025134 : ∀ q ∈ ArchTree.t025134.leavesR [4, 3, 1, 5, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0013.paths ++ Cs.C0014.paths).drop 301).take 3909 := by
    rw [← sub_025134]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0013.leafOK Cs.C0014.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `025135`: 656 archived leaves (DFS range 42215..42870). -/
theorem sub_025135 : (ArchTree.t025135.leavesR [5, 3, 1, 5, 2, 0]).map Prod.fst =
    ((Cs.C0014.paths ++ Cs.C0015.paths).drop 193).take 656 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_025135 : ∀ q ∈ ArchTree.t025135.leavesR [5, 3, 1, 5, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0014.paths ++ Cs.C0015.paths).drop 193).take 656 := by
    rw [← sub_025135]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0014.leafOK Cs.C0015.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end CKLaneN6.Asm

import CKLaneN6.Tree
import CKLaneN6.AsmBase
import CKLaneN6.Cs.C0015
import CKLaneN6.Cs.C0016

/-! Lane N6 assembly part 1: depth-6 subtrees 034024..035135 of the archived tree, each
matched (kernel decide over the overlapping coarse shards only) with the shard leaf lists. -/

set_option autoImplicit false

namespace CKLaneN6.Asm

open CKLaneN6 CKLaneM05.FE8

set_option maxHeartbeats 0 in
/-- Subtree `034024`: 1 archived leaves (DFS range 42871..42871). -/
theorem sub_034024 : (ArchTree.t034024.leavesR [4, 2, 0, 4, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 249).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_034024 : ∀ q ∈ ArchTree.t034024.leavesR [4, 2, 0, 4, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 249).take 1 := by
    rw [← sub_034024]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `034025`: 1 archived leaves (DFS range 42872..42872). -/
theorem sub_034025 : (ArchTree.t034025.leavesR [5, 2, 0, 4, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 250).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_034025 : ∀ q ∈ ArchTree.t034025.leavesR [5, 2, 0, 4, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 250).take 1 := by
    rw [← sub_034025]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `034034`: 1 archived leaves (DFS range 42873..42873). -/
theorem sub_034034 : (ArchTree.t034034.leavesR [4, 3, 0, 4, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 251).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_034034 : ∀ q ∈ ArchTree.t034034.leavesR [4, 3, 0, 4, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 251).take 1 := by
    rw [← sub_034034]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `034035`: 1 archived leaves (DFS range 42874..42874). -/
theorem sub_034035 : (ArchTree.t034035.leavesR [5, 3, 0, 4, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 252).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_034035 : ∀ q ∈ ArchTree.t034035.leavesR [5, 3, 0, 4, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 252).take 1 := by
    rw [← sub_034035]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `034124`: 1170 archived leaves (DFS range 42875..44044). -/
theorem sub_034124 : (ArchTree.t034124.leavesR [4, 2, 1, 4, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 253).take 1170 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_034124 : ∀ q ∈ ArchTree.t034124.leavesR [4, 2, 1, 4, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 253).take 1170 := by
    rw [← sub_034124]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `034125`: 2001 archived leaves (DFS range 44045..46045). -/
theorem sub_034125 : (ArchTree.t034125.leavesR [5, 2, 1, 4, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 1423).take 2001 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_034125 : ∀ q ∈ ArchTree.t034125.leavesR [5, 2, 1, 4, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 1423).take 2001 := by
    rw [← sub_034125]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `034134`: 1 archived leaves (DFS range 46046..46046). -/
theorem sub_034134 : (ArchTree.t034134.leavesR [4, 3, 1, 4, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 3424).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_034134 : ∀ q ∈ ArchTree.t034134.leavesR [4, 3, 1, 4, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 3424).take 1 := by
    rw [← sub_034134]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `034135`: 1 archived leaves (DFS range 46047..46047). -/
theorem sub_034135 : (ArchTree.t034135.leavesR [5, 3, 1, 4, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 3425).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_034135 : ∀ q ∈ ArchTree.t034135.leavesR [5, 3, 1, 4, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 3425).take 1 := by
    rw [← sub_034135]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `035024`: 1 archived leaves (DFS range 46048..46048). -/
theorem sub_035024 : (ArchTree.t035024.leavesR [4, 2, 0, 5, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 3426).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_035024 : ∀ q ∈ ArchTree.t035024.leavesR [4, 2, 0, 5, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 3426).take 1 := by
    rw [← sub_035024]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `035025`: 1 archived leaves (DFS range 46049..46049). -/
theorem sub_035025 : (ArchTree.t035025.leavesR [5, 2, 0, 5, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 3427).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_035025 : ∀ q ∈ ArchTree.t035025.leavesR [5, 2, 0, 5, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 3427).take 1 := by
    rw [← sub_035025]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `035034`: 1 archived leaves (DFS range 46050..46050). -/
theorem sub_035034 : (ArchTree.t035034.leavesR [4, 3, 0, 5, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 3428).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_035034 : ∀ q ∈ ArchTree.t035034.leavesR [4, 3, 0, 5, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 3428).take 1 := by
    rw [← sub_035034]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `035035`: 1 archived leaves (DFS range 46051..46051). -/
theorem sub_035035 : (ArchTree.t035035.leavesR [5, 3, 0, 5, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths).drop 3429).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_035035 : ∀ q ∈ ArchTree.t035035.leavesR [5, 3, 0, 5, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths).drop 3429).take 1 := by
    rw [← sub_035035]; exact List.mem_map_of_mem hq
  exact Cs.C0015.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `035124`: 1110 archived leaves (DFS range 46052..47161). -/
theorem sub_035124 : (ArchTree.t035124.leavesR [4, 2, 1, 5, 3, 0]).map Prod.fst =
    ((Cs.C0015.paths ++ Cs.C0016.paths).drop 3430).take 1110 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_035124 : ∀ q ∈ ArchTree.t035124.leavesR [4, 2, 1, 5, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0015.paths ++ Cs.C0016.paths).drop 3430).take 1110 := by
    rw [← sub_035124]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0015.leafOK Cs.C0016.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `035125`: 321 archived leaves (DFS range 47162..47482). -/
theorem sub_035125 : (ArchTree.t035125.leavesR [5, 2, 1, 5, 3, 0]).map Prod.fst =
    ((Cs.C0016.paths).drop 322).take 321 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_035125 : ∀ q ∈ ArchTree.t035125.leavesR [5, 2, 1, 5, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 322).take 321 := by
    rw [← sub_035125]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `035134`: 1 archived leaves (DFS range 47483..47483). -/
theorem sub_035134 : (ArchTree.t035134.leavesR [4, 3, 1, 5, 3, 0]).map Prod.fst =
    ((Cs.C0016.paths).drop 643).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_035134 : ∀ q ∈ ArchTree.t035134.leavesR [4, 3, 1, 5, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 643).take 1 := by
    rw [← sub_035134]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `035135`: 1 archived leaves (DFS range 47484..47484). -/
theorem sub_035135 : (ArchTree.t035135.leavesR [5, 3, 1, 5, 3, 0]).map Prod.fst =
    ((Cs.C0016.paths).drop 644).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_035135 : ∀ q ∈ ArchTree.t035135.leavesR [5, 3, 1, 5, 3, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 644).take 1 := by
    rw [← sub_035135]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end CKLaneN6.Asm

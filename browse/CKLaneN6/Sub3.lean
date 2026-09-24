import CKLaneN6.Tree
import CKLaneN6.AsmBase
import CKLaneN6.Cs.C0016
import CKLaneN6.Cs.C0017
import CKLaneN6.Cs.C0018
import CKLaneN6.Cs.C0019
import CKLaneN6.Cs.C0020
import CKLaneN6.Cs.C0021
import CKLaneN6.Cs.C0022
import CKLaneN6.Cs.C0023
import CKLaneN6.Cs.C0024
import CKLaneN6.Cs.C0025
import CKLaneN6.Cs.C0026
import CKLaneN6.Cs.C0027
import CKLaneN6.Cs.C0028
import CKLaneN6.Cs.C0029
import CKLaneN6.Cs.C0030
import CKLaneN6.Cs.C0031
import CKLaneN6.Cs.C0032
import CKLaneN6.Cs.C0033
import CKLaneN6.Cs.C0034
import CKLaneN6.Cs.C0035
import CKLaneN6.Cs.C0036
import CKLaneN6.Cs.C0037
import CKLaneN6.Cs.C0038
import CKLaneN6.Cs.C0039
import CKLaneN6.Cs.C0040
import CKLaneN6.Cs.C0041
import CKLaneN6.Cs.C0042
import CKLaneN6.Cs.C0043
import CKLaneN6.Cs.C0044
import CKLaneN6.Cs.C0045
import CKLaneN6.Cs.C0046
import CKLaneN6.Cs.C0047
import CKLaneN6.Cs.C0048
import CKLaneN6.Cs.C0049
import CKLaneN6.Cs.C0050
import CKLaneN6.Cs.C0051
import CKLaneN6.Cs.C0052
import CKLaneN6.Cs.C0053
import CKLaneN6.Cs.C0054
import CKLaneN6.Cs.C0055
import CKLaneN6.Cs.C0056
import CKLaneN6.Cs.C0057
import CKLaneN6.Cs.C0058
import CKLaneN6.Cs.C0059
import CKLaneN6.Cs.C0060
import CKLaneN6.Cs.C0061
import CKLaneN6.Cs.C0062

/-! Lane N6 assembly part 3: depth-6 subtrees 134024..135135 of the archived tree, each
matched (kernel decide over the overlapping coarse shards only) with the shard leaf lists. -/

set_option autoImplicit false

namespace CKLaneN6.Asm

open CKLaneN6 CKLaneM05.FE8

set_option maxHeartbeats 0 in
/-- Subtree `134024`: 1144 archived leaves (DFS range 47501..48644). -/
theorem sub_134024 : (ArchTree.t134024.leavesR [4, 2, 0, 4, 3, 1]).map Prod.fst =
    ((Cs.C0016.paths ++ Cs.C0017.paths ++ Cs.C0018.paths).drop 661).take 1144 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134024 : ∀ q ∈ ArchTree.t134024.leavesR [4, 2, 0, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths ++ Cs.C0017.paths ++ Cs.C0018.paths).drop 661).take 1144 := by
    rw [← sub_134024]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' (forall_mem_append' Cs.C0016.leafOK Cs.C0017.leafOK) Cs.C0018.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `134025`: 1077 archived leaves (DFS range 48645..49721). -/
theorem sub_134025 : (ArchTree.t134025.leavesR [5, 2, 0, 4, 3, 1]).map Prod.fst =
    ((Cs.C0018.paths ++ Cs.C0019.paths).drop 128).take 1077 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134025 : ∀ q ∈ ArchTree.t134025.leavesR [5, 2, 0, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0018.paths ++ Cs.C0019.paths).drop 128).take 1077 := by
    rw [← sub_134025]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0018.leafOK Cs.C0019.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `134034`: 463 archived leaves (DFS range 49722..50184). -/
theorem sub_134034 : (ArchTree.t134034.leavesR [4, 3, 0, 4, 3, 1]).map Prod.fst =
    ((Cs.C0019.paths ++ Cs.C0020.paths ++ Cs.C0021.paths).drop 252).take 463 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134034 : ∀ q ∈ ArchTree.t134034.leavesR [4, 3, 0, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0019.paths ++ Cs.C0020.paths ++ Cs.C0021.paths).drop 252).take 463 := by
    rw [← sub_134034]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' (forall_mem_append' Cs.C0019.leafOK Cs.C0020.leafOK) Cs.C0021.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `134035`: 212 archived leaves (DFS range 50185..50396). -/
theorem sub_134035 : (ArchTree.t134035.leavesR [5, 3, 0, 4, 3, 1]).map Prod.fst =
    ((Cs.C0021.paths).drop 15).take 212 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134035 : ∀ q ∈ ArchTree.t134035.leavesR [5, 3, 0, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0021.paths).drop 15).take 212 := by
    rw [← sub_134035]; exact List.mem_map_of_mem hq
  exact Cs.C0021.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `134124`: 1 archived leaves (DFS range 50397..50397). -/
theorem sub_134124 : (ArchTree.t134124.leavesR [4, 2, 1, 4, 3, 1]).map Prod.fst =
    ((Cs.C0021.paths).drop 227).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134124 : ∀ q ∈ ArchTree.t134124.leavesR [4, 2, 1, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0021.paths).drop 227).take 1 := by
    rw [← sub_134124]; exact List.mem_map_of_mem hq
  exact Cs.C0021.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `134125`: 1 archived leaves (DFS range 50398..50398). -/
theorem sub_134125 : (ArchTree.t134125.leavesR [5, 2, 1, 4, 3, 1]).map Prod.fst =
    ((Cs.C0021.paths).drop 228).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134125 : ∀ q ∈ ArchTree.t134125.leavesR [5, 2, 1, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0021.paths).drop 228).take 1 := by
    rw [← sub_134125]; exact List.mem_map_of_mem hq
  exact Cs.C0021.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `134134`: 21954 archived leaves (DFS range 50399..72352). -/
theorem sub_134134 : (ArchTree.t134134.leavesR [4, 3, 1, 4, 3, 1]).map Prod.fst =
    ((Cs.C0021.paths ++ Cs.C0022.paths ++ Cs.C0023.paths ++ Cs.C0024.paths ++ Cs.C0025.paths ++ Cs.C0026.paths ++ Cs.C0027.paths ++ Cs.C0028.paths ++ Cs.C0029.paths ++ Cs.C0030.paths ++ Cs.C0031.paths ++ Cs.C0032.paths ++ Cs.C0033.paths ++ Cs.C0034.paths ++ Cs.C0035.paths ++ Cs.C0036.paths ++ Cs.C0037.paths ++ Cs.C0038.paths ++ Cs.C0039.paths ++ Cs.C0040.paths ++ Cs.C0041.paths ++ Cs.C0042.paths ++ Cs.C0043.paths ++ Cs.C0044.paths ++ Cs.C0045.paths ++ Cs.C0046.paths ++ Cs.C0047.paths ++ Cs.C0048.paths ++ Cs.C0049.paths ++ Cs.C0050.paths ++ Cs.C0051.paths ++ Cs.C0052.paths ++ Cs.C0053.paths ++ Cs.C0054.paths ++ Cs.C0055.paths ++ Cs.C0056.paths ++ Cs.C0057.paths ++ Cs.C0058.paths).drop 229).take 21954 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134134 : ∀ q ∈ ArchTree.t134134.leavesR [4, 3, 1, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0021.paths ++ Cs.C0022.paths ++ Cs.C0023.paths ++ Cs.C0024.paths ++ Cs.C0025.paths ++ Cs.C0026.paths ++ Cs.C0027.paths ++ Cs.C0028.paths ++ Cs.C0029.paths ++ Cs.C0030.paths ++ Cs.C0031.paths ++ Cs.C0032.paths ++ Cs.C0033.paths ++ Cs.C0034.paths ++ Cs.C0035.paths ++ Cs.C0036.paths ++ Cs.C0037.paths ++ Cs.C0038.paths ++ Cs.C0039.paths ++ Cs.C0040.paths ++ Cs.C0041.paths ++ Cs.C0042.paths ++ Cs.C0043.paths ++ Cs.C0044.paths ++ Cs.C0045.paths ++ Cs.C0046.paths ++ Cs.C0047.paths ++ Cs.C0048.paths ++ Cs.C0049.paths ++ Cs.C0050.paths ++ Cs.C0051.paths ++ Cs.C0052.paths ++ Cs.C0053.paths ++ Cs.C0054.paths ++ Cs.C0055.paths ++ Cs.C0056.paths ++ Cs.C0057.paths ++ Cs.C0058.paths).drop 229).take 21954 := by
    rw [← sub_134134]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' (forall_mem_append' Cs.C0021.leafOK Cs.C0022.leafOK) Cs.C0023.leafOK) Cs.C0024.leafOK) Cs.C0025.leafOK) Cs.C0026.leafOK) Cs.C0027.leafOK) Cs.C0028.leafOK) Cs.C0029.leafOK) Cs.C0030.leafOK) Cs.C0031.leafOK) Cs.C0032.leafOK) Cs.C0033.leafOK) Cs.C0034.leafOK) Cs.C0035.leafOK) Cs.C0036.leafOK) Cs.C0037.leafOK) Cs.C0038.leafOK) Cs.C0039.leafOK) Cs.C0040.leafOK) Cs.C0041.leafOK) Cs.C0042.leafOK) Cs.C0043.leafOK) Cs.C0044.leafOK) Cs.C0045.leafOK) Cs.C0046.leafOK) Cs.C0047.leafOK) Cs.C0048.leafOK) Cs.C0049.leafOK) Cs.C0050.leafOK) Cs.C0051.leafOK) Cs.C0052.leafOK) Cs.C0053.leafOK) Cs.C0054.leafOK) Cs.C0055.leafOK) Cs.C0056.leafOK) Cs.C0057.leafOK) Cs.C0058.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `134135`: 977 archived leaves (DFS range 72353..73329). -/
theorem sub_134135 : (ArchTree.t134135.leavesR [5, 3, 1, 4, 3, 1]).map Prod.fst =
    ((Cs.C0058.paths ++ Cs.C0059.paths).drop 91).take 977 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134135 : ∀ q ∈ ArchTree.t134135.leavesR [5, 3, 1, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0058.paths ++ Cs.C0059.paths).drop 91).take 977 := by
    rw [← sub_134135]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0058.leafOK Cs.C0059.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135024`: 697 archived leaves (DFS range 73330..74026). -/
theorem sub_135024 : (ArchTree.t135024.leavesR [4, 2, 0, 5, 3, 1]).map Prod.fst =
    ((Cs.C0059.paths ++ Cs.C0060.paths).drop 702).take 697 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135024 : ∀ q ∈ ArchTree.t135024.leavesR [4, 2, 0, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0059.paths ++ Cs.C0060.paths).drop 702).take 697 := by
    rw [← sub_135024]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0059.leafOK Cs.C0060.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135025`: 790 archived leaves (DFS range 74027..74816). -/
theorem sub_135025 : (ArchTree.t135025.leavesR [5, 2, 0, 5, 3, 1]).map Prod.fst =
    ((Cs.C0060.paths).drop 425).take 790 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135025 : ∀ q ∈ ArchTree.t135025.leavesR [5, 2, 0, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0060.paths).drop 425).take 790 := by
    rw [← sub_135025]; exact List.mem_map_of_mem hq
  exact Cs.C0060.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135034`: 163 archived leaves (DFS range 74817..74979). -/
theorem sub_135034 : (ArchTree.t135034.leavesR [4, 3, 0, 5, 3, 1]).map Prod.fst =
    ((Cs.C0060.paths ++ Cs.C0061.paths).drop 1215).take 163 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135034 : ∀ q ∈ ArchTree.t135034.leavesR [4, 3, 0, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0060.paths ++ Cs.C0061.paths).drop 1215).take 163 := by
    rw [← sub_135034]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0060.leafOK Cs.C0061.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135035`: 321 archived leaves (DFS range 74980..75300). -/
theorem sub_135035 : (ArchTree.t135035.leavesR [5, 3, 0, 5, 3, 1]).map Prod.fst =
    ((Cs.C0061.paths).drop 12).take 321 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135035 : ∀ q ∈ ArchTree.t135035.leavesR [5, 3, 0, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0061.paths).drop 12).take 321 := by
    rw [← sub_135035]; exact List.mem_map_of_mem hq
  exact Cs.C0061.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135124`: 1 archived leaves (DFS range 75301..75301). -/
theorem sub_135124 : (ArchTree.t135124.leavesR [4, 2, 1, 5, 3, 1]).map Prod.fst =
    ((Cs.C0061.paths).drop 333).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135124 : ∀ q ∈ ArchTree.t135124.leavesR [4, 2, 1, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0061.paths).drop 333).take 1 := by
    rw [← sub_135124]; exact List.mem_map_of_mem hq
  exact Cs.C0061.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135125`: 1 archived leaves (DFS range 75302..75302). -/
theorem sub_135125 : (ArchTree.t135125.leavesR [5, 2, 1, 5, 3, 1]).map Prod.fst =
    ((Cs.C0061.paths).drop 334).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135125 : ∀ q ∈ ArchTree.t135125.leavesR [5, 2, 1, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0061.paths).drop 334).take 1 := by
    rw [← sub_135125]; exact List.mem_map_of_mem hq
  exact Cs.C0061.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135134`: 454 archived leaves (DFS range 75303..75756). -/
theorem sub_135134 : (ArchTree.t135134.leavesR [4, 3, 1, 5, 3, 1]).map Prod.fst =
    ((Cs.C0061.paths).drop 335).take 454 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135134 : ∀ q ∈ ArchTree.t135134.leavesR [4, 3, 1, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0061.paths).drop 335).take 454 := by
    rw [← sub_135134]; exact List.mem_map_of_mem hq
  exact Cs.C0061.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135135`: 790 archived leaves (DFS range 75757..76546). -/
theorem sub_135135 : (ArchTree.t135135.leavesR [5, 3, 1, 5, 3, 1]).map Prod.fst =
    ((Cs.C0061.paths ++ Cs.C0062.paths).drop 789).take 790 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135135 : ∀ q ∈ ArchTree.t135135.leavesR [5, 3, 1, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0061.paths ++ Cs.C0062.paths).drop 789).take 790 := by
    rw [← sub_135135]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0061.leafOK Cs.C0062.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end CKLaneN6.Asm

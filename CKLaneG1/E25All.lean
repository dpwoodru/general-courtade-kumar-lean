import CKLaneG1.E25S.S0000
import CKLaneG1.E25S.S0001
import CKLaneG1.E25S.S0002
import CKLaneG1.E25S.S0003
import CKLaneG1.E25S.S0004
import CKLaneG1.E25S.S0005
import CKLaneG1.E25S.S0006
import CKLaneG1.E25S.S0007
import CKLaneG1.E25S.S0008
import CKLaneG1.E25S.S0009
import CKLaneG1.E25S.S0010
import CKLaneG1.E25S.S0011
import CKLaneG1.E25S.S0012
import CKLaneG1.E25S.S0013
import CKLaneG1.E25S.S0014
import CKLaneG1.E25S.S0015
import CKLaneG1.E25S.S0016

/-!
# Lane G1: union of the E ≤ 1/25 certificate shards

`all` = the 4,178 archived (O) leaves classified `le` in `G1/trees/archiveO/e25_index_v1.json`
(shards `CKLaneG1.E25S.S0000..S0016`); `all_le`: each of their clipped physical images
`CKLaneD.InUVT (uvtBox p)` lies in `E ≤ 1/25` (the region delegated to OUTER_OPPOSITE_LOW_ENTROPY).
-/

namespace CKLaneG1.E25All

open CKLaneD CKLaneG1

def all : List (List ℕ × EW) :=
  E25S.S0000.leaves ++ (E25S.S0001.leaves ++ (E25S.S0002.leaves ++ (E25S.S0003.leaves ++ (E25S.S0004.leaves ++ (E25S.S0005.leaves ++ (E25S.S0006.leaves ++ (E25S.S0007.leaves ++ (E25S.S0008.leaves ++ (E25S.S0009.leaves ++ (E25S.S0010.leaves ++ (E25S.S0011.leaves ++ (E25S.S0012.leaves ++ (E25S.S0013.leaves ++ (E25S.S0014.leaves ++ (E25S.S0015.leaves ++ (E25S.S0016.leaves))))))))))))))))

theorem all_length : all.length = 4178 := by decide +kernel

theorem all_le : ∀ x ∈ all, ∀ a b E : ℝ, InUVT (uvtBox x.1) a b E → E ≤ 1 / 25 := by
  intro x hx
  simp only [all, List.mem_append] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  exacts [E25S.S0000.le x h, E25S.S0001.le x h, E25S.S0002.le x h, E25S.S0003.le x h, E25S.S0004.le x h, E25S.S0005.le x h, E25S.S0006.le x h, E25S.S0007.le x h, E25S.S0008.le x h, E25S.S0009.le x h, E25S.S0010.le x h, E25S.S0011.le x h, E25S.S0012.le x h, E25S.S0013.le x h, E25S.S0014.le x h, E25S.S0015.le x h, E25S.S0016.le x h]

end CKLaneG1.E25All

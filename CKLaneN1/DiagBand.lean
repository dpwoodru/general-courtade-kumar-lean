import CKLaneN1.DBShard.D00
import CKLaneN1.DBShard.D01
import CKLaneN1.DBShard.D02
import CKLaneN1.DBShard.D03
import CKLaneN1.DBShard.D04
import CKLaneN1.DBShard.D05
import CKLaneN1.DBShard.D06
import CKLaneN1.DBShard.D07
import CKLaneN1.DBShard.D08
import CKLaneN1.DBRow
import CKLaneN1.Chunks

/-!
# Lane N1: NO_SEP §6 cover and the row `NoSepA_ModerateRest` (N23 row 4)

All 325 archived DIAGONAL_BAND leaves pass the kernel check (`dbTree_ok`). The 153 endpoint and
140 log-sum leaves are certified. The 32 prior-cap leaves are certified vacuous in this row
(`I⁺ ≤ 3/40` contradicts `s > 3/40`).
-/

namespace CKLaneN1

theorem dbTree_length : dbTree.leaves.length = 325 := by decide +kernel

/-- Every archived NO_SEP §6 leaf passes the kernel check. -/
theorem dbTree_ok : dbTree.allLeaves dbLeafOK = true := by
  unfold PT.allLeaves
  apply all_of_chunks (fun q => dbLeafOK q.1 q.2) 40 9 dbTree.leaves (by rw [dbTree_length]; decide)
  intro k hk
  interval_cases k
  · exact DBShard.D00
  · exact DBShard.D01
  · exact DBShard.D02
  · exact DBShard.D03
  · exact DBShard.D04
  · exact DBShard.D05
  · exact DBShard.D06
  · exact DBShard.D07
  · exact DBShard.D08

/-- Row 4 (N23): NO_SEP §6 outside the prior-cap leaves. -/
theorem row_noSepA_moderateRest : NoSepA_ModerateRest :=
  noSepA_moderateRest_of_tree dbTree_ok

end CKLaneN1

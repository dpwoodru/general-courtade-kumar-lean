import CKLaneN1.DBTree

/-! Kernel check of archived dbTree leaves [120, 160). -/

namespace CKLaneN1.DBShard

theorem D03 : ((dbTree.leaves.drop 120).take 40).all
    (fun q => dbLeafOK q.1 q.2) = true := by decide +kernel

end CKLaneN1.DBShard

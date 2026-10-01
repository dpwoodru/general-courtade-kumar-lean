import CKLaneN1.DBTree

/-! Kernel check of archived dbTree leaves [280, 320). -/

namespace CKLaneN1.DBShard

theorem D07 : ((dbTree.leaves.drop 280).take 40).all
    (fun q => dbLeafOK q.1 q.2) = true := by decide +kernel

end CKLaneN1.DBShard

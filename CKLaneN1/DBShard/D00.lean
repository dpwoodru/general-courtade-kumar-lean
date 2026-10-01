import CKLaneN1.DBTree

/-! Kernel check of archived dbTree leaves [0, 40). -/

namespace CKLaneN1.DBShard

theorem D00 : ((dbTree.leaves.drop 0).take 40).all
    (fun q => dbLeafOK q.1 q.2) = true := by decide +kernel

end CKLaneN1.DBShard

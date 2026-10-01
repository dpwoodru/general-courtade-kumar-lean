import CKLaneN1.DBTree

/-! Kernel check of archived dbTree leaves [40, 80). -/

namespace CKLaneN1.DBShard

theorem D01 : ((dbTree.leaves.drop 40).take 40).all
    (fun q => dbLeafOK q.1 q.2) = true := by decide +kernel

end CKLaneN1.DBShard

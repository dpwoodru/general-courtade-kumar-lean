import CKLaneN1.DBTree

/-! Kernel check of archived dbTree leaves [240, 280). -/

namespace CKLaneN1.DBShard

theorem D06 : ((dbTree.leaves.drop 240).take 40).all
    (fun q => dbLeafOK q.1 q.2) = true := by decide +kernel

end CKLaneN1.DBShard

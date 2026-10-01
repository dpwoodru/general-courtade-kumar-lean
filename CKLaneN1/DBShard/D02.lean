import CKLaneN1.DBTree

/-! Kernel check of archived dbTree leaves [80, 120). -/

namespace CKLaneN1.DBShard

theorem D02 : ((dbTree.leaves.drop 80).take 40).all
    (fun q => dbLeafOK q.1 q.2) = true := by decide +kernel

end CKLaneN1.DBShard

import CKLaneN1.DBTree

/-! Kernel check of archived dbTree leaves [200, 240). -/

namespace CKLaneN1.DBShard

theorem D05 : ((dbTree.leaves.drop 200).take 40).all
    (fun q => dbLeafOK q.1 q.2) = true := by decide +kernel

end CKLaneN1.DBShard

import CKLaneN1.SRTrees

/-! Kernel check of archived centralTree leaves [520, 560). -/

namespace CKLaneN1.SRShard

theorem T13 : ((centralTree.leaves.drop 520).take 40).all
    (fun q => leafOK4 q.1 q.2) = true := by decide +kernel

end CKLaneN1.SRShard

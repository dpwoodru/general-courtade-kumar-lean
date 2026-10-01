import CKLaneN1.SRTrees

/-! Kernel check of archived centralTree leaves [160, 200). -/

namespace CKLaneN1.SRShard

theorem T04 : ((centralTree.leaves.drop 160).take 40).all
    (fun q => leafOK4 q.1 q.2) = true := by decide +kernel

end CKLaneN1.SRShard

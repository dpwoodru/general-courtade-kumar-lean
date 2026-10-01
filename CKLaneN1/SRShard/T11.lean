import CKLaneN1.SRTrees

/-! Kernel check of archived centralTree leaves [440, 480). -/

namespace CKLaneN1.SRShard

theorem T11 : ((centralTree.leaves.drop 440).take 40).all
    (fun q => leafOK4 q.1 q.2) = true := by decide +kernel

end CKLaneN1.SRShard

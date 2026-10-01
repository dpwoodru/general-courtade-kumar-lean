import CKLaneN1.SRTrees

/-! Kernel check of archived centralTree leaves [600, 611). -/

namespace CKLaneN1.SRShard

theorem T15 : ((centralTree.leaves.drop 600).take 40).all
    (fun q => leafOK4 q.1 q.2) = true := by decide +kernel

end CKLaneN1.SRShard

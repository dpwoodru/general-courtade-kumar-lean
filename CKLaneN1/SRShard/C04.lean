import CKLaneN1.SRTrees

/-! Kernel check of archived collarTree leaves [160, 200). -/

namespace CKLaneN1.SRShard

theorem C04 : ((collarTree.leaves.drop 160).take 40).all
    (fun q => leafOKC q.1 q.2) = true := by decide +kernel

end CKLaneN1.SRShard

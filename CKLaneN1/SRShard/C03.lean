import CKLaneN1.SRTrees

/-! Kernel check of archived collarTree leaves [120, 160). -/

namespace CKLaneN1.SRShard

theorem C03 : ((collarTree.leaves.drop 120).take 40).all
    (fun q => leafOKC q.1 q.2) = true := by decide +kernel

end CKLaneN1.SRShard

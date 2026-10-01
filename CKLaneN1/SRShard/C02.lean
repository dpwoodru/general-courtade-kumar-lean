import CKLaneN1.SRTrees

/-! Kernel check of archived collarTree leaves [80, 120). -/

namespace CKLaneN1.SRShard

theorem C02 : ((collarTree.leaves.drop 80).take 40).all
    (fun q => leafOKC q.1 q.2) = true := by decide +kernel

end CKLaneN1.SRShard

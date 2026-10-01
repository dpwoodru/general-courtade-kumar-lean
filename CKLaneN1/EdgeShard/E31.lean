import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [1550, 1600). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E31 : ((edgeTree.leaves.drop 1550).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

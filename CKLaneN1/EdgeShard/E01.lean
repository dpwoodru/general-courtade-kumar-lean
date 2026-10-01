import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [50, 100). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E01 : ((edgeTree.leaves.drop 50).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

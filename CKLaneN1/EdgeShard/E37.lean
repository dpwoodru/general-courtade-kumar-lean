import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [1850, 1900). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E37 : ((edgeTree.leaves.drop 1850).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

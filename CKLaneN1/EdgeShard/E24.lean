import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [1200, 1250). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E24 : ((edgeTree.leaves.drop 1200).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

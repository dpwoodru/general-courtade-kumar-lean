import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [2550, 2600). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E51 : ((edgeTree.leaves.drop 2550).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

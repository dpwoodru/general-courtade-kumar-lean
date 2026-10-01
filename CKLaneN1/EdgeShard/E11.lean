import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [550, 600). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E11 : ((edgeTree.leaves.drop 550).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

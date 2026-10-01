import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [1300, 1350). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E26 : ((edgeTree.leaves.drop 1300).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

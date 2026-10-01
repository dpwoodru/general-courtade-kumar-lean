import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [300, 350). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E06 : ((edgeTree.leaves.drop 300).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

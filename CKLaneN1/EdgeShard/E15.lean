import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [750, 800). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E15 : ((edgeTree.leaves.drop 750).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

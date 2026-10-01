import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [1750, 1800). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E35 : ((edgeTree.leaves.drop 1750).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

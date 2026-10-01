import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [1400, 1450). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E28 : ((edgeTree.leaves.drop 1400).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

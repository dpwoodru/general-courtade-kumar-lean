import CKLaneN1.EdgeTree

/-! Kernel check of generated edgeTree leaves [350, 400). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E07 : ((edgeTree.leaves.drop 350).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

import CKLaneN1.CapTree

/-! Kernel check of generated capTree leaves [480, 531). -/

namespace CKLaneN1.CapShard

open CKLaneN1.Capital

theorem K08 : ((capTree.leaves.drop 480).take 60).all
    (fun q => capLeafOK (capRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.CapShard

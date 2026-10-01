import CKLaneN1.CapTree

/-! Kernel check of generated capTree leaves [420, 480). -/

namespace CKLaneN1.CapShard

open CKLaneN1.Capital

theorem K07 : ((capTree.leaves.drop 420).take 60).all
    (fun q => capLeafOK (capRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.CapShard

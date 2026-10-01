import CKLaneN1.CapTree

/-! Kernel check of generated capTree leaves [180, 240). -/

namespace CKLaneN1.CapShard

open CKLaneN1.Capital

theorem K03 : ((capTree.leaves.drop 180).take 60).all
    (fun q => capLeafOK (capRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.CapShard

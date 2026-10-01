import GeneralCK.Certificates.E8TAxisRationalTreeBridgeKernel

namespace GeneralCK.Certificates.E8TAxisFullBridge.Geometry
open E8TAxisPartitionKernel E8TAxisGeneratedGeometry E8TAxisRationalTreeBridgeKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem historical_tree_valid : qValid tree qDomain := by
  apply qValid_of_bool
  decide +kernel

theorem historical_leaves_in_cells :
    ∀ q ∈ qLeaves tree qDomain, q ∈ cells := by decide +kernel

#print axioms historical_tree_valid
#print axioms historical_leaves_in_cells
end GeneralCK.Certificates.E8TAxisFullBridge.Geometry

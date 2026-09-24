import CKLaneN23.UCon

/-! Kernel evaluation of one part of the corner checker (Lane N23b): `ucCheck = true` by `decide +kernel`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CKLaneN23.CT

theorem uc_ok : ucCheck = true := by decide +kernel

end CKLaneN23.CT

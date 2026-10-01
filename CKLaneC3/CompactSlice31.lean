import CKLaneC3.CompactBatch31
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch31 = slice 31 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice31
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch31.tags.map tagRect = CompactTreeA.rects31 := by
  decide +kernel

end CKLaneC3.CompactSlice31

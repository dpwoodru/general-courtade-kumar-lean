import CKLaneC3.CompactBatch16
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch16 = slice 16 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice16
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch16.tags.map tagRect = CompactTreeA.rects16 := by
  decide +kernel

end CKLaneC3.CompactSlice16

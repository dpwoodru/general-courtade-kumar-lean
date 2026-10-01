import CKLaneC3.CompactBatch00
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch00 = slice 00 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice00
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch00.tags.map tagRect = CompactTreeA.rects00 := by
  decide +kernel

end CKLaneC3.CompactSlice00

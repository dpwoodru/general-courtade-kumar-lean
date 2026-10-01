import CKLaneC3.CompactBatch37
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch37 = slice 37 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice37
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch37.tags.map tagRect = CompactTreeA.rects37 := by
  decide +kernel

end CKLaneC3.CompactSlice37

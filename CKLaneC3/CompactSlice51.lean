import CKLaneC3.CompactBatch51
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch51 = slice 51 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice51
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch51.tags.map tagRect = CompactTreeA.rects51 := by
  decide +kernel

end CKLaneC3.CompactSlice51

import CKLaneC3.CompactBatch28
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch28 = slice 28 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice28
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch28.tags.map tagRect = CompactTreeA.rects28 := by
  decide +kernel

end CKLaneC3.CompactSlice28

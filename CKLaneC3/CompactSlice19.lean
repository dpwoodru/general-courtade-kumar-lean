import CKLaneC3.CompactBatch19
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch19 = slice 19 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice19
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch19.tags.map tagRect = CompactTreeA.rects19 := by
  decide +kernel

end CKLaneC3.CompactSlice19

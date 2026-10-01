import CKLaneC3.CompactBatch39
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch39 = slice 39 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice39
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch39.tags.map tagRect = CompactTreeA.rects39 := by
  decide +kernel

end CKLaneC3.CompactSlice39

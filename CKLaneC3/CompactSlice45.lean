import CKLaneC3.CompactBatch45
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch45 = slice 45 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice45
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch45.tags.map tagRect = CompactTreeA.rects45 := by
  decide +kernel

end CKLaneC3.CompactSlice45

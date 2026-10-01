import CKLaneC3.CompactBatch08
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch08 = slice 08 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice08
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch08.tags.map tagRect = CompactTreeA.rects08 := by
  decide +kernel

end CKLaneC3.CompactSlice08

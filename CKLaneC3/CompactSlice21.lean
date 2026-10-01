import CKLaneC3.CompactBatch21
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch21 = slice 21 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice21
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch21.tags.map tagRect = CompactTreeA.rects21 := by
  decide +kernel

end CKLaneC3.CompactSlice21

import CKLaneC3.CompactBatch29
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch29 = slice 29 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice29
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch29.tags.map tagRect = CompactTreeA.rects29 := by
  decide +kernel

end CKLaneC3.CompactSlice29

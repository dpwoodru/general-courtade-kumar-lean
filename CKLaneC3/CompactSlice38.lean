import CKLaneC3.CompactBatch38
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch38 = slice 38 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice38
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch38.tags.map tagRect = CompactTreeA.rects38 := by
  decide +kernel

end CKLaneC3.CompactSlice38

import CKLaneC3.CompactBatch14
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch14 = slice 14 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice14
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch14.tags.map tagRect = CompactTreeA.rects14 := by
  decide +kernel

end CKLaneC3.CompactSlice14

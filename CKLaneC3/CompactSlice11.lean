import CKLaneC3.CompactBatch11
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch11 = slice 11 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice11
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch11.tags.map tagRect = CompactTreeA.rects11 := by
  decide +kernel

end CKLaneC3.CompactSlice11

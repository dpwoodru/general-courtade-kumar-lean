import CKLaneC3.CompactBatch35
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch35 = slice 35 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice35
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch35.tags.map tagRect = CompactTreeA.rects35 := by
  decide +kernel

end CKLaneC3.CompactSlice35

import CKLaneC3.CompactBatch05
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch05 = slice 05 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice05
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch05.tags.map tagRect = CompactTreeA.rects05 := by
  decide +kernel

end CKLaneC3.CompactSlice05

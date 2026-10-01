import CKLaneC3.CompactBatch23
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch23 = slice 23 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice23
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch23.tags.map tagRect = CompactTreeA.rects23 := by
  decide +kernel

end CKLaneC3.CompactSlice23

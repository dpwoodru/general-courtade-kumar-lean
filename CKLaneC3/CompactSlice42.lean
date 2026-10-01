import CKLaneC3.CompactBatch42
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch42 = slice 42 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice42
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch42.tags.map tagRect = CompactTreeA.rects42 := by
  decide +kernel

end CKLaneC3.CompactSlice42

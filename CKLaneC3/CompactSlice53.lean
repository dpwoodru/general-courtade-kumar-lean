import CKLaneC3.CompactBatch53
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch53 = slice 53 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice53
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch53.tags.map tagRect = CompactTreeA.rects53 := by
  decide +kernel

end CKLaneC3.CompactSlice53

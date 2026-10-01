import CKLaneC3.CompactBatch30
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch30 = slice 30 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice30
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch30.tags.map tagRect = CompactTreeA.rects30 := by
  decide +kernel

end CKLaneC3.CompactSlice30

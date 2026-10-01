import CKLaneC3.CompactBatch43
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch43 = slice 43 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice43
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch43.tags.map tagRect = CompactTreeA.rects43 := by
  decide +kernel

end CKLaneC3.CompactSlice43

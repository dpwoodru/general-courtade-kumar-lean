import CKLaneC3.CompactBatch47
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch47 = slice 47 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice47
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch47.tags.map tagRect = CompactTreeA.rects47 := by
  decide +kernel

end CKLaneC3.CompactSlice47

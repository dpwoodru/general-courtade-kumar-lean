import CKLaneC3.CompactBatch34
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch34 = slice 34 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice34
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch34.tags.map tagRect = CompactTreeA.rects34 := by
  decide +kernel

end CKLaneC3.CompactSlice34

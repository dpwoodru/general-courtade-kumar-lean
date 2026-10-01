import CKLaneC3.CompactBatch12
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch12 = slice 12 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice12
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch12.tags.map tagRect = CompactTreeA.rects12 := by
  decide +kernel

end CKLaneC3.CompactSlice12

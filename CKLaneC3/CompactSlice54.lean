import CKLaneC3.CompactBatch54
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch54 = slice 54 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice54
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch54.tags.map tagRect = CompactTreeA.rects54 := by
  decide +kernel

end CKLaneC3.CompactSlice54

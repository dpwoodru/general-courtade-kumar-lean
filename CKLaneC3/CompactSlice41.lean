import CKLaneC3.CompactBatch41
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch41 = slice 41 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice41
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch41.tags.map tagRect = CompactTreeA.rects41 := by
  decide +kernel

end CKLaneC3.CompactSlice41

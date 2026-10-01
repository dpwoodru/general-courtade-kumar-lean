import CKLaneC3.CompactBatch33
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch33 = slice 33 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice33
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch33.tags.map tagRect = CompactTreeA.rects33 := by
  decide +kernel

end CKLaneC3.CompactSlice33

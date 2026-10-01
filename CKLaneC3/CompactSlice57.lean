import CKLaneC3.CompactBatch57
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch57 = slice 57 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice57
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch57.tags.map tagRect = CompactTreeA.rects57 := by
  decide +kernel

end CKLaneC3.CompactSlice57

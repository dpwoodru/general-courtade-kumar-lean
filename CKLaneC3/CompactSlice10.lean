import CKLaneC3.CompactBatch10
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch10 = slice 10 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice10
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch10.tags.map tagRect = CompactTreeA.rects10 := by
  decide +kernel

end CKLaneC3.CompactSlice10

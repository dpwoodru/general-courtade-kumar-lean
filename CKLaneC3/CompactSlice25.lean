import CKLaneC3.CompactBatch25
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch25 = slice 25 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice25
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch25.tags.map tagRect = CompactTreeA.rects25 := by
  decide +kernel

end CKLaneC3.CompactSlice25

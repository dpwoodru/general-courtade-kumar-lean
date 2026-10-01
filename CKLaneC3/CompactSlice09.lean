import CKLaneC3.CompactBatch09
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch09 = slice 09 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice09
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch09.tags.map tagRect = CompactTreeA.rects09 := by
  decide +kernel

end CKLaneC3.CompactSlice09

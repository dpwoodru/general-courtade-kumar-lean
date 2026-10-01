import CKLaneC3.CompactBatch40
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch40 = slice 40 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice40
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch40.tags.map tagRect = CompactTreeA.rects40 := by
  decide +kernel

end CKLaneC3.CompactSlice40

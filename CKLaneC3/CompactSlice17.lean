import CKLaneC3.CompactBatch17
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch17 = slice 17 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice17
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch17.tags.map tagRect = CompactTreeA.rects17 := by
  decide +kernel

end CKLaneC3.CompactSlice17

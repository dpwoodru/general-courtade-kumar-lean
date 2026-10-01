import CKLaneC3.CompactBatch26
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch26 = slice 26 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice26
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch26.tags.map tagRect = CompactTreeA.rects26 := by
  decide +kernel

end CKLaneC3.CompactSlice26

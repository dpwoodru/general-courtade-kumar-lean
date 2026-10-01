import CKLaneC3.CompactBatch03
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch03 = slice 03 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice03
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch03.tags.map tagRect = CompactTreeA.rects03 := by
  decide +kernel

end CKLaneC3.CompactSlice03

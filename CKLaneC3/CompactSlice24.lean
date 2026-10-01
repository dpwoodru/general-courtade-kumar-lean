import CKLaneC3.CompactBatch24
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch24 = slice 24 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice24
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch24.tags.map tagRect = CompactTreeA.rects24 := by
  decide +kernel

end CKLaneC3.CompactSlice24

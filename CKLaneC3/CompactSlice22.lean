import CKLaneC3.CompactBatch22
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch22 = slice 22 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice22
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch22.tags.map tagRect = CompactTreeA.rects22 := by
  decide +kernel

end CKLaneC3.CompactSlice22

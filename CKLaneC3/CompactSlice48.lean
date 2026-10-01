import CKLaneC3.CompactBatch48
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch48 = slice 48 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice48
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch48.tags.map tagRect = CompactTreeA.rects48 := by
  decide +kernel

end CKLaneC3.CompactSlice48

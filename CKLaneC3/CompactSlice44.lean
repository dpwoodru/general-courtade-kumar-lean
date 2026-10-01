import CKLaneC3.CompactBatch44
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch44 = slice 44 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice44
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch44.tags.map tagRect = CompactTreeA.rects44 := by
  decide +kernel

end CKLaneC3.CompactSlice44

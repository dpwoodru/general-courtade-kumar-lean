import CKLaneC3.CompactBatch18
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch18 = slice 18 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice18
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch18.tags.map tagRect = CompactTreeA.rects18 := by
  decide +kernel

end CKLaneC3.CompactSlice18

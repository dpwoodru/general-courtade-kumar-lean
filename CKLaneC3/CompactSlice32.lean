import CKLaneC3.CompactBatch32
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch32 = slice 32 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice32
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch32.tags.map tagRect = CompactTreeA.rects32 := by
  decide +kernel

end CKLaneC3.CompactSlice32

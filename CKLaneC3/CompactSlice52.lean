import CKLaneC3.CompactBatch52
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch52 = slice 52 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice52
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch52.tags.map tagRect = CompactTreeA.rects52 := by
  decide +kernel

end CKLaneC3.CompactSlice52

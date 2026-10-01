import CKLaneC3.CompactBatch27
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch27 = slice 27 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice27
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch27.tags.map tagRect = CompactTreeA.rects27 := by
  decide +kernel

end CKLaneC3.CompactSlice27

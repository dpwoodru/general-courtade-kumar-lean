import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 3)`: kernel evaluation of `boxCell 0 3` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_3 : boxCell 0 3 = true := by decide +kernel

end CKLaneN23.CT

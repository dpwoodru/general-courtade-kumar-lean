import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 8)`: kernel evaluation of `boxCell 1 8` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_8 : boxCell 1 8 = true := by decide +kernel

end CKLaneN23.CT

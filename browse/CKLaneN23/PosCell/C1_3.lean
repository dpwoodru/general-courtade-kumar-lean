import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 3)`: kernel evaluation of `boxCell 1 3` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_3 : boxCell 1 3 = true := by decide +kernel

end CKLaneN23.CT

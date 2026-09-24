import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 4)`: kernel evaluation of `boxCell 1 4` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_4 : boxCell 1 4 = true := by decide +kernel

end CKLaneN23.CT

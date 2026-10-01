import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 15)`: kernel evaluation of `boxCell 1 15` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_15 : boxCell 1 15 = true := by decide +kernel

end CKLaneN23.CT

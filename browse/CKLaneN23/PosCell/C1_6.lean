import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 6)`: kernel evaluation of `boxCell 1 6` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_6 : boxCell 1 6 = true := by decide +kernel

end CKLaneN23.CT

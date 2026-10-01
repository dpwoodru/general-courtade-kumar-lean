import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 12)`: kernel evaluation of `boxCell 1 12` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_12 : boxCell 1 12 = true := by decide +kernel

end CKLaneN23.CT

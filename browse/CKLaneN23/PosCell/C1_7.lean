import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 7)`: kernel evaluation of `boxCell 1 7` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_7 : boxCell 1 7 = true := by decide +kernel

end CKLaneN23.CT

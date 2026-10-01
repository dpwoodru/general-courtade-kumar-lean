import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 14)`: kernel evaluation of `boxCell 1 14` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_14 : boxCell 1 14 = true := by decide +kernel

end CKLaneN23.CT

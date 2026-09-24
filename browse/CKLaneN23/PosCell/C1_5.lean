import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 5)`: kernel evaluation of `boxCell 1 5` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_5 : boxCell 1 5 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 13)`: kernel evaluation of `boxCell 1 13` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_13 : boxCell 1 13 = true := by decide +kernel

end CKLaneN23.CT

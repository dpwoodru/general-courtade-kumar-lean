import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 1)`: kernel evaluation of `boxCell 1 1` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_1 : boxCell 1 1 = true := by decide +kernel

end CKLaneN23.CT

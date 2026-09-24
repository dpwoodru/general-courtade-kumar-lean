import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 2)`: kernel evaluation of `boxCell 1 2` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_2 : boxCell 1 2 = true := by decide +kernel

end CKLaneN23.CT

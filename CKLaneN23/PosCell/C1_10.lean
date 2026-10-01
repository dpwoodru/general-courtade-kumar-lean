import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 10)`: kernel evaluation of `boxCell 1 10` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_10 : boxCell 1 10 = true := by decide +kernel

end CKLaneN23.CT

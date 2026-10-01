import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 0)`: kernel evaluation of `boxCell 1 0` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_0 : boxCell 1 0 = true := by decide +kernel

end CKLaneN23.CT

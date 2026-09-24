import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 1)`: kernel evaluation of `boxCell 3 1` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_1 : boxCell 3 1 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 1)`: kernel evaluation of `boxCell 7 1` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_1 : boxCell 7 1 = true := by decide +kernel

end CKLaneN23.CT

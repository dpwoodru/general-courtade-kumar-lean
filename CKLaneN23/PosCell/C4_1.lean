import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 1)`: kernel evaluation of `boxCell 4 1` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_1 : boxCell 4 1 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 1)`: kernel evaluation of `boxCell 2 1` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_1 : boxCell 2 1 = true := by decide +kernel

end CKLaneN23.CT

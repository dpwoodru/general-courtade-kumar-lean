import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 4)`: kernel evaluation of `boxCell 7 4` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_4 : boxCell 7 4 = true := by decide +kernel

end CKLaneN23.CT

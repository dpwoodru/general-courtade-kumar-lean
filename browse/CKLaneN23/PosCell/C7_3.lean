import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 3)`: kernel evaluation of `boxCell 7 3` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_3 : boxCell 7 3 = true := by decide +kernel

end CKLaneN23.CT

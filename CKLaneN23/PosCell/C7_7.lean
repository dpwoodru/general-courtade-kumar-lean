import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 7)`: kernel evaluation of `boxCell 7 7` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_7 : boxCell 7 7 = true := by decide +kernel

end CKLaneN23.CT

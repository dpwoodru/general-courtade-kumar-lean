import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 15)`: kernel evaluation of `boxCell 7 15` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_15 : boxCell 7 15 = true := by decide +kernel

end CKLaneN23.CT

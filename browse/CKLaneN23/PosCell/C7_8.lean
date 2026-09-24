import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 8)`: kernel evaluation of `boxCell 7 8` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_8 : boxCell 7 8 = true := by decide +kernel

end CKLaneN23.CT

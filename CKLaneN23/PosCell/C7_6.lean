import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 6)`: kernel evaluation of `boxCell 7 6` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_6 : boxCell 7 6 = true := by decide +kernel

end CKLaneN23.CT

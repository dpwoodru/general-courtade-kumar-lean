import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 12)`: kernel evaluation of `boxCell 7 12` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_12 : boxCell 7 12 = true := by decide +kernel

end CKLaneN23.CT

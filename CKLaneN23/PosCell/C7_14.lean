import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 14)`: kernel evaluation of `boxCell 7 14` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_14 : boxCell 7 14 = true := by decide +kernel

end CKLaneN23.CT

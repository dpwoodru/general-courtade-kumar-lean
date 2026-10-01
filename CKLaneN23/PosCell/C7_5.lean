import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 5)`: kernel evaluation of `boxCell 7 5` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_5 : boxCell 7 5 = true := by decide +kernel

end CKLaneN23.CT

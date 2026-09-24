import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 7)`: kernel evaluation of `boxCell 3 7` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_7 : boxCell 3 7 = true := by decide +kernel

end CKLaneN23.CT

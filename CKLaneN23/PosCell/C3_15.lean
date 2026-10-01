import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 15)`: kernel evaluation of `boxCell 3 15` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_15 : boxCell 3 15 = true := by decide +kernel

end CKLaneN23.CT

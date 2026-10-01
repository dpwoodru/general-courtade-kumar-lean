import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 15)`: kernel evaluation of `boxCell 4 15` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_15 : boxCell 4 15 = true := by decide +kernel

end CKLaneN23.CT

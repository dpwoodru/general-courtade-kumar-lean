import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 15)`: kernel evaluation of `boxCell 2 15` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_15 : boxCell 2 15 = true := by decide +kernel

end CKLaneN23.CT

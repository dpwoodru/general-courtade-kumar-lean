import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 3)`: kernel evaluation of `boxCell 3 3` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_3 : boxCell 3 3 = true := by decide +kernel

end CKLaneN23.CT

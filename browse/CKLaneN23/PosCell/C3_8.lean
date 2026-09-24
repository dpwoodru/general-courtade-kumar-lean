import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 8)`: kernel evaluation of `boxCell 3 8` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_8 : boxCell 3 8 = true := by decide +kernel

end CKLaneN23.CT

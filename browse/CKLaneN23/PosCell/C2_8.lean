import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 8)`: kernel evaluation of `boxCell 2 8` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_8 : boxCell 2 8 = true := by decide +kernel

end CKLaneN23.CT

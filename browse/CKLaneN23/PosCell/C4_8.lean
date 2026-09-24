import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 8)`: kernel evaluation of `boxCell 4 8` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_8 : boxCell 4 8 = true := by decide +kernel

end CKLaneN23.CT

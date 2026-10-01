import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 3)`: kernel evaluation of `boxCell 4 3` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_3 : boxCell 4 3 = true := by decide +kernel

end CKLaneN23.CT

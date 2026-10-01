import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 3)`: kernel evaluation of `boxCell 2 3` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_3 : boxCell 2 3 = true := by decide +kernel

end CKLaneN23.CT

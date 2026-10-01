import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 4)`: kernel evaluation of `boxCell 3 4` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_4 : boxCell 3 4 = true := by decide +kernel

end CKLaneN23.CT

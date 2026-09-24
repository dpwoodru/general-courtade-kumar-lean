import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 2)`: kernel evaluation of `boxCell 3 2` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_2 : boxCell 3 2 = true := by decide +kernel

end CKLaneN23.CT

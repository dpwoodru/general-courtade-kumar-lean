import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 13)`: kernel evaluation of `boxCell 3 13` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_13 : boxCell 3 13 = true := by decide +kernel

end CKLaneN23.CT

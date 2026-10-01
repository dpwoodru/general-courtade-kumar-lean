import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 13)`: kernel evaluation of `boxCell 7 13` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_13 : boxCell 7 13 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 2)`: kernel evaluation of `boxCell 7 2` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_2 : boxCell 7 2 = true := by decide +kernel

end CKLaneN23.CT

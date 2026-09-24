import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 7)`: kernel evaluation of `boxCell 2 7` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_7 : boxCell 2 7 = true := by decide +kernel

end CKLaneN23.CT

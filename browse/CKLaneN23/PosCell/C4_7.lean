import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 7)`: kernel evaluation of `boxCell 4 7` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_7 : boxCell 4 7 = true := by decide +kernel

end CKLaneN23.CT

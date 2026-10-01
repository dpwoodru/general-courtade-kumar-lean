import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 11)`: kernel evaluation of `boxCell 7 11` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_11 : boxCell 7 11 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 11)`: kernel evaluation of `boxCell 3 11` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_11 : boxCell 3 11 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 11)`: kernel evaluation of `boxCell 4 11` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_11 : boxCell 4 11 = true := by decide +kernel

end CKLaneN23.CT

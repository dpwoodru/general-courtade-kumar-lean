import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 11)`: kernel evaluation of `boxCell 2 11` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_11 : boxCell 2 11 = true := by decide +kernel

end CKLaneN23.CT

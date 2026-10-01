import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 11)`: kernel evaluation of `boxCell 6 11` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_11 : boxCell 6 11 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 11)`: kernel evaluation of `boxCell 5 11` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_11 : boxCell 5 11 = true := by decide +kernel

end CKLaneN23.CT

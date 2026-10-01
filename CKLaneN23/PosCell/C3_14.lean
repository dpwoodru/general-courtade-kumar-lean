import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 14)`: kernel evaluation of `boxCell 3 14` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_14 : boxCell 3 14 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 14)`: kernel evaluation of `boxCell 4 14` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_14 : boxCell 4 14 = true := by decide +kernel

end CKLaneN23.CT

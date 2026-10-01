import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 14)`: kernel evaluation of `boxCell 2 14` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_14 : boxCell 2 14 = true := by decide +kernel

end CKLaneN23.CT

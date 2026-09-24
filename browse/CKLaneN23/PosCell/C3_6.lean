import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 6)`: kernel evaluation of `boxCell 3 6` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_6 : boxCell 3 6 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 6)`: kernel evaluation of `boxCell 2 6` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_6 : boxCell 2 6 = true := by decide +kernel

end CKLaneN23.CT

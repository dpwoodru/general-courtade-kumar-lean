import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 6)`: kernel evaluation of `boxCell 4 6` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_6 : boxCell 4 6 = true := by decide +kernel

end CKLaneN23.CT

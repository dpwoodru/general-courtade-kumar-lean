import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 6)`: kernel evaluation of `boxCell 0 6` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_6 : boxCell 0 6 = true := by decide +kernel

end CKLaneN23.CT

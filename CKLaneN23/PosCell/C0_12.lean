import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 12)`: kernel evaluation of `boxCell 0 12` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_12 : boxCell 0 12 = true := by decide +kernel

end CKLaneN23.CT

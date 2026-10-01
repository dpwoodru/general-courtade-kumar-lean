import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 15)`: kernel evaluation of `boxCell 0 15` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_15 : boxCell 0 15 = true := by decide +kernel

end CKLaneN23.CT

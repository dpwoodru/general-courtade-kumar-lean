import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 1)`: kernel evaluation of `boxCell 0 1` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_1 : boxCell 0 1 = true := by decide +kernel

end CKLaneN23.CT

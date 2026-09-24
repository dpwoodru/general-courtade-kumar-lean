import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 4)`: kernel evaluation of `boxCell 0 4` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_4 : boxCell 0 4 = true := by decide +kernel

end CKLaneN23.CT

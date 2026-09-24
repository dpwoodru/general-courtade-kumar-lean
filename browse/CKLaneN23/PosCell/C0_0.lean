import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 0)`: kernel evaluation of `boxCell 0 0` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_0 : boxCell 0 0 = true := by decide +kernel

end CKLaneN23.CT

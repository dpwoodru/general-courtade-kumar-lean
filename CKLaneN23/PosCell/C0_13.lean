import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 13)`: kernel evaluation of `boxCell 0 13` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_13 : boxCell 0 13 = true := by decide +kernel

end CKLaneN23.CT

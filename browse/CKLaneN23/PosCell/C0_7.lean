import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 7)`: kernel evaluation of `boxCell 0 7` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_7 : boxCell 0 7 = true := by decide +kernel

end CKLaneN23.CT

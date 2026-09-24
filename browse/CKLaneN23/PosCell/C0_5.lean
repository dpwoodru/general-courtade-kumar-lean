import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 5)`: kernel evaluation of `boxCell 0 5` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_5 : boxCell 0 5 = true := by decide +kernel

end CKLaneN23.CT

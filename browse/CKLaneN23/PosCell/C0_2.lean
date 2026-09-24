import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 2)`: kernel evaluation of `boxCell 0 2` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_2 : boxCell 0 2 = true := by decide +kernel

end CKLaneN23.CT

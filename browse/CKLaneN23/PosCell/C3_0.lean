import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 0)`: kernel evaluation of `boxCell 3 0` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_0 : boxCell 3 0 = true := by decide +kernel

end CKLaneN23.CT

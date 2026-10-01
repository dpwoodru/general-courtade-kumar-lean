import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 0)`: kernel evaluation of `boxCell 7 0` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_0 : boxCell 7 0 = true := by decide +kernel

end CKLaneN23.CT

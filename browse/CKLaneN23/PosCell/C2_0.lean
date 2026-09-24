import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 0)`: kernel evaluation of `boxCell 2 0` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_0 : boxCell 2 0 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 0)`: kernel evaluation of `boxCell 4 0` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_0 : boxCell 4 0 = true := by decide +kernel

end CKLaneN23.CT

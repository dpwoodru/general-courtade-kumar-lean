import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 0)`: kernel evaluation of `boxCell 6 0` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_0 : boxCell 6 0 = true := by decide +kernel

end CKLaneN23.CT

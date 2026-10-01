import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 1)`: kernel evaluation of `boxCell 6 1` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_1 : boxCell 6 1 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 3)`: kernel evaluation of `boxCell 6 3` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_3 : boxCell 6 3 = true := by decide +kernel

end CKLaneN23.CT

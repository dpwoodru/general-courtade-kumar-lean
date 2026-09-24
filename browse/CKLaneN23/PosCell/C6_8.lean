import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 8)`: kernel evaluation of `boxCell 6 8` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_8 : boxCell 6 8 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 12)`: kernel evaluation of `boxCell 3 12` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_12 : boxCell 3 12 = true := by decide +kernel

end CKLaneN23.CT

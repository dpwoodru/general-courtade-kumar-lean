import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 12)`: kernel evaluation of `boxCell 4 12` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_12 : boxCell 4 12 = true := by decide +kernel

end CKLaneN23.CT

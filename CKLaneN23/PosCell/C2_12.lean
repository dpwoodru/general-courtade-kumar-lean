import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 12)`: kernel evaluation of `boxCell 2 12` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_12 : boxCell 2 12 = true := by decide +kernel

end CKLaneN23.CT

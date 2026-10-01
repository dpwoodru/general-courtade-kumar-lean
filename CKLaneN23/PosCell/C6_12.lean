import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 12)`: kernel evaluation of `boxCell 6 12` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_12 : boxCell 6 12 = true := by decide +kernel

end CKLaneN23.CT

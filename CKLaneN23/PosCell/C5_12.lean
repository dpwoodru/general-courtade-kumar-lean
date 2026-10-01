import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 12)`: kernel evaluation of `boxCell 5 12` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_12 : boxCell 5 12 = true := by decide +kernel

end CKLaneN23.CT

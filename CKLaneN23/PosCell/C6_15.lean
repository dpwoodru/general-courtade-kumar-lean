import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 15)`: kernel evaluation of `boxCell 6 15` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_15 : boxCell 6 15 = true := by decide +kernel

end CKLaneN23.CT

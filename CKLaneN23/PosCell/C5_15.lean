import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 15)`: kernel evaluation of `boxCell 5 15` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_15 : boxCell 5 15 = true := by decide +kernel

end CKLaneN23.CT

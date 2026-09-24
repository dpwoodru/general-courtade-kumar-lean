import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 5)`: kernel evaluation of `boxCell 3 5` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_5 : boxCell 3 5 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 10)`: kernel evaluation of `boxCell 3 10` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_10 : boxCell 3 10 = true := by decide +kernel

end CKLaneN23.CT

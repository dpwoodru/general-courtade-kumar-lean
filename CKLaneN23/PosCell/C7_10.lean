import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 10)`: kernel evaluation of `boxCell 7 10` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_10 : boxCell 7 10 = true := by decide +kernel

end CKLaneN23.CT

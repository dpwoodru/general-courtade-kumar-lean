import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 10)`: kernel evaluation of `boxCell 4 10` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_10 : boxCell 4 10 = true := by decide +kernel

end CKLaneN23.CT

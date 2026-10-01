import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 10)`: kernel evaluation of `boxCell 2 10` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_10 : boxCell 2 10 = true := by decide +kernel

end CKLaneN23.CT

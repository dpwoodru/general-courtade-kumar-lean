import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 10)`: kernel evaluation of `boxCell 6 10` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_10 : boxCell 6 10 = true := by decide +kernel

end CKLaneN23.CT

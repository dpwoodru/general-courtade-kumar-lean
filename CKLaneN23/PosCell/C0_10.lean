import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 10)`: kernel evaluation of `boxCell 0 10` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_10 : boxCell 0 10 = true := by decide +kernel

end CKLaneN23.CT

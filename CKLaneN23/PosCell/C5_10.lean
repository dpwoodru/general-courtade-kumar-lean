import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 10)`: kernel evaluation of `boxCell 5 10` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_10 : boxCell 5 10 = true := by decide +kernel

end CKLaneN23.CT

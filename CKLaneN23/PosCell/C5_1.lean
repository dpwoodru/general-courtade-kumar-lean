import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 1)`: kernel evaluation of `boxCell 5 1` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_1 : boxCell 5 1 = true := by decide +kernel

end CKLaneN23.CT

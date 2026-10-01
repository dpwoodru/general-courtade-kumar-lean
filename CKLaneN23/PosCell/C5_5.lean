import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 5)`: kernel evaluation of `boxCell 5 5` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_5 : boxCell 5 5 = true := by decide +kernel

end CKLaneN23.CT

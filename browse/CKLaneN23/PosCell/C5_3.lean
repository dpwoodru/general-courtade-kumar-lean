import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 3)`: kernel evaluation of `boxCell 5 3` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_3 : boxCell 5 3 = true := by decide +kernel

end CKLaneN23.CT

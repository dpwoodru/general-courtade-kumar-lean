import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 5)`: kernel evaluation of `boxCell 2 5` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_5 : boxCell 2 5 = true := by decide +kernel

end CKLaneN23.CT

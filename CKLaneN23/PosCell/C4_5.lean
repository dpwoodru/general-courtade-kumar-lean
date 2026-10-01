import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 5)`: kernel evaluation of `boxCell 4 5` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_5 : boxCell 4 5 = true := by decide +kernel

end CKLaneN23.CT

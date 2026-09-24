import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 2)`: kernel evaluation of `boxCell 4 2` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_2 : boxCell 4 2 = true := by decide +kernel

end CKLaneN23.CT

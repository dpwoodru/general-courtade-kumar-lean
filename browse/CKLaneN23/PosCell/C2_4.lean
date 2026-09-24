import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 4)`: kernel evaluation of `boxCell 2 4` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_4 : boxCell 2 4 = true := by decide +kernel

end CKLaneN23.CT

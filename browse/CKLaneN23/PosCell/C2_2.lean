import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 2)`: kernel evaluation of `boxCell 2 2` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_2 : boxCell 2 2 = true := by decide +kernel

end CKLaneN23.CT

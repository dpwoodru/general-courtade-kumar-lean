import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 4)`: kernel evaluation of `boxCell 4 4` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_4 : boxCell 4 4 = true := by decide +kernel

end CKLaneN23.CT

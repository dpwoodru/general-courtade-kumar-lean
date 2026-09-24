import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 4)`: kernel evaluation of `boxCell 6 4` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_4 : boxCell 6 4 = true := by decide +kernel

end CKLaneN23.CT

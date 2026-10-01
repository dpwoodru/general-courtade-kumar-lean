import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 13)`: kernel evaluation of `boxCell 4 13` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_13 : boxCell 4 13 = true := by decide +kernel

end CKLaneN23.CT

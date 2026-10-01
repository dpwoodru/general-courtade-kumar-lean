import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 13)`: kernel evaluation of `boxCell 2 13` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_13 : boxCell 2 13 = true := by decide +kernel

end CKLaneN23.CT

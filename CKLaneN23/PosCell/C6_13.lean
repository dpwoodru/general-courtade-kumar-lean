import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 13)`: kernel evaluation of `boxCell 6 13` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_13 : boxCell 6 13 = true := by decide +kernel

end CKLaneN23.CT

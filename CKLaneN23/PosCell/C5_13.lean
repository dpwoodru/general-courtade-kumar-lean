import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 13)`: kernel evaluation of `boxCell 5 13` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_13 : boxCell 5 13 = true := by decide +kernel

end CKLaneN23.CT

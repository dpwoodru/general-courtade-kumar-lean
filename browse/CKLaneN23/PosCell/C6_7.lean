import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 7)`: kernel evaluation of `boxCell 6 7` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_7 : boxCell 6 7 = true := by decide +kernel

end CKLaneN23.CT

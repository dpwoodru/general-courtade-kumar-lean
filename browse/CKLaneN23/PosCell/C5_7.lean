import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 7)`: kernel evaluation of `boxCell 5 7` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_7 : boxCell 5 7 = true := by decide +kernel

end CKLaneN23.CT

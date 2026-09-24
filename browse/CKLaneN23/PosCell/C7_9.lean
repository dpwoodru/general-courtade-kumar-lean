import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(7, 9)`: kernel evaluation of `boxCell 7 9` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_7_9 : boxCell 7 9 = true := by decide +kernel

end CKLaneN23.CT

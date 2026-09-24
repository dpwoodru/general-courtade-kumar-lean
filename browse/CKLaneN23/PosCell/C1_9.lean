import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(1, 9)`: kernel evaluation of `boxCell 1 9` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_1_9 : boxCell 1 9 = true := by decide +kernel

end CKLaneN23.CT

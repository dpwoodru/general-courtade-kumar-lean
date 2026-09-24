import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(3, 9)`: kernel evaluation of `boxCell 3 9` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_3_9 : boxCell 3 9 = true := by decide +kernel

end CKLaneN23.CT

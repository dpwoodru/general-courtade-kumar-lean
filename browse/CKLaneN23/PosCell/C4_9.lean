import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(4, 9)`: kernel evaluation of `boxCell 4 9` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_9 : boxCell 4 9 = true := by decide +kernel

end CKLaneN23.CT

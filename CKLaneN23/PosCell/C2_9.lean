import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(2, 9)`: kernel evaluation of `boxCell 2 9` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_2_9 : boxCell 2 9 = true := by decide +kernel

end CKLaneN23.CT

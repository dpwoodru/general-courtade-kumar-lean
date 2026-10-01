import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 9)`: kernel evaluation of `boxCell 0 9` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_9 : boxCell 0 9 = true := by decide +kernel

end CKLaneN23.CT

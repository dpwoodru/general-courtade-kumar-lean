import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 9)`: kernel evaluation of `boxCell 6 9` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_9 : boxCell 6 9 = true := by decide +kernel

end CKLaneN23.CT

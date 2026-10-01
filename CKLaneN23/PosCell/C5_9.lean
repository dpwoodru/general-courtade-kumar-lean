import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 9)`: kernel evaluation of `boxCell 5 9` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_9 : boxCell 5 9 = true := by decide +kernel

end CKLaneN23.CT

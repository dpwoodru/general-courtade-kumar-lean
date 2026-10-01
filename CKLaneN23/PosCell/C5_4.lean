import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 4)`: kernel evaluation of `boxCell 5 4` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_4 : boxCell 5 4 = true := by decide +kernel

end CKLaneN23.CT

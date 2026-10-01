import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 8)`: kernel evaluation of `boxCell 5 8` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_8 : boxCell 5 8 = true := by decide +kernel

end CKLaneN23.CT

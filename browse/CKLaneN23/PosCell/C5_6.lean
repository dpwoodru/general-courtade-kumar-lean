import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 6)`: kernel evaluation of `boxCell 5 6` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_6 : boxCell 5 6 = true := by decide +kernel

end CKLaneN23.CT

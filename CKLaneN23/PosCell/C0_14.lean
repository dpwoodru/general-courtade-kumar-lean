import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 14)`: kernel evaluation of `boxCell 0 14` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_14 : boxCell 0 14 = true := by decide +kernel

end CKLaneN23.CT

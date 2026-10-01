import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 14)`: kernel evaluation of `boxCell 6 14` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_14 : boxCell 6 14 = true := by decide +kernel

end CKLaneN23.CT

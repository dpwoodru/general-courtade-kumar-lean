import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 14)`: kernel evaluation of `boxCell 5 14` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_14 : boxCell 5 14 = true := by decide +kernel

end CKLaneN23.CT

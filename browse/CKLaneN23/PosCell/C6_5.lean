import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 5)`: kernel evaluation of `boxCell 6 5` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_5 : boxCell 6 5 = true := by decide +kernel

end CKLaneN23.CT

import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(6, 2)`: kernel evaluation of `boxCell 6 2` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_6_2 : boxCell 6 2 = true := by decide +kernel

end CKLaneN23.CT

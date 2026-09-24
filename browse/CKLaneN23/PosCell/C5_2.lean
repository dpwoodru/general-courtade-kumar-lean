import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 2)`: kernel evaluation of `boxCell 5 2` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_2 : boxCell 5 2 = true := by decide +kernel

end CKLaneN23.CT

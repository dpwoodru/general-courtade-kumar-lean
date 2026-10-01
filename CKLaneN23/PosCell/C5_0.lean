import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(5, 0)`: kernel evaluation of `boxCell 5 0` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_5_0 : boxCell 5 0 = true := by decide +kernel

end CKLaneN23.CT

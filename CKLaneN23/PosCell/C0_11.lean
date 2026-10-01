import CKLaneN23.CPosSplit

/-! Corner positivity grid cell `(0, 11)`: kernel evaluation of `boxCell 0 11` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_0_11 : boxCell 0 11 = true := by decide +kernel

end CKLaneN23.CT

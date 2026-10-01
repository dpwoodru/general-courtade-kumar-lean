import CKLaneN23.CStep2

/-!
# CKLaneN23.CQ — compact rational literals for large certificate data (Lane N23b)

`qq n d = n / d`.  Certificate literals written with `qq` elaborate much faster than `((n : ℚ) / d)`
(no `binop%` elaboration per coefficient); the kernel evaluates `qq n d` to the normalized rational.
-/

namespace CKLaneN23.CT

/-- `n / d` as a rational -/
def qq (n : ℤ) (d : ℕ) : ℚ := (n : ℚ) / (d : ℚ)

end CKLaneN23.CT

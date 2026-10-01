import CKLaneN23.CStep2

/-!
# CKLaneN23.CSemT — small semantic facts used inside the trivariate corner chain (Lane N23b)
-/

namespace CKLaneN23.CT

open GeneralCK

theorem hent_le_one (z : ℝ) : hent z ≤ 1 := H_le_one _

/-- `ε = 1 - (a+b)/2 ≥ 0` (scaled by 5) when `a, b ≤ 1` — the argument of the eta series. -/
theorem eps_nonneg_chain (a b : ℝ) (ha : a ≤ 1) (hb : b ≤ 1) :
    0 ≤ (((5 : ℚ) : ℚ) : ℝ) * (LPoly.eval (Real.log 2) [(0, (1 : ℚ))] +
      (((-1 : ℚ) : ℚ) : ℝ) * (((((1 : ℚ) / 2) : ℚ) : ℝ) * (a + b))) := by
  rw [LPoly.eval_c]
  push_cast
  nlinarith

end CKLaneN23.CT

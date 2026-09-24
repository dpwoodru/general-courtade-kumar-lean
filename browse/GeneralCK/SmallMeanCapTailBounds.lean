import GeneralCK.LowInformationMeans

/-! Elementary real inequalities used by the high double-cap endpoint.
The strict interval avoids the singularity at bias one. -/

namespace GeneralCK.SmallMean
open Set

/-- The first two positive terms of the atanh series, from mathlib's
proved lower bound for its partial sums. -/
theorem A_ge_linear_cubic {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    r + r ^ 3 / 3 ≤ A r := by
  have h := Real.sum_range_le_log_div hr hr' 2
  norm_num [Finset.sum_range_succ] at h
  unfold A
  linarith

/-- A rational upper bound for the natural-unit entropy deficit near bias
zero. Its leading quadratic coefficient is exact. -/
theorem Cn_le_half_sq_over_gap {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    Cn r ≤ r ^ 2 / (2 * (1 - r ^ 2)) := by
  have hn : 0 < 1 - r ^ 2 := by nlinarith [hr, hr']
  have hstrong := LowInformation.Cn_upper_sharp hr hr'
  have hstep : r ^ 2 / 2 + r ^ 4 / (12 * (1 - r ^ 2)) ≤
      r ^ 2 / (2 * (1 - r ^ 2)) := by
    have heq : r ^ 2 / (2 * (1 - r ^ 2)) -
        (r ^ 2 / 2 + r ^ 4 / (12 * (1 - r ^ 2))) =
        5 * r ^ 4 / (12 * (1 - r ^ 2)) := by
      field_simp [hn.ne']
      ring
    have hp : 0 ≤ 5 * r ^ 4 / (12 * (1 - r ^ 2)) := by positivity
    linarith
  exact hstrong.trans hstep

#print axioms A_ge_linear_cubic
#print axioms Cn_le_half_sq_over_gap

end GeneralCK.SmallMean

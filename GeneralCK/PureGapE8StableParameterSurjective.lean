import GeneralCK.Certificates.E8TAxisStableScalar

/-!
# Surjectivity of the stable E8 parameter on the positive slope range

The interval certificates use the hyperbolic parameter `a`, whereas the
analytic consumer is stated for an arbitrary member of `e8SlopeRange`.
This file gives the exact bridge between those two coordinates.  It does
not use a numerical approximation or a global inverse theorem: the witness
is constructed from the already-defined radial contact.
-/

namespace GeneralCK

open Set Reflection Certificates.Reflection
open Certificates.E8TAxisStableScalar

/-- Every positive E8 slope is exactly `Y a` for a positive stable
parameter.  This is the coverage bridge needed by an alpha-space interval
certificate for logarithmic convexity. -/
theorem e8SlopeRange_exists_stable_parameter {y : ℝ}
    (hy : y ∈ e8SlopeRange) :
    ∃ a : ℝ, 0 < a ∧ Y a = y := by
  obtain ⟨x, hx, hxy⟩ := hy
  have hx0 : 0 < x := by simpa only [mem_Ioi] using hx
  let v : ℝ := radialContact (2 * x) 1
  let c : ℝ := 1 - 2 * v
  let a : ℝ := SmallMean.A c
  have hv : 0 < v := by
    dsimp only [v]
    exact radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1 / 2 := by
    dsimp only [v]
    exact radialContact_lt_half (by positivity) (by norm_num)
  have hv1 : v < 1 := hvh.trans (by norm_num)
  have hc : 0 < c := by dsimp only [c]; linarith
  have hc1 : c < 1 := by dsimp only [c]; linarith
  have ha : 0 < a := by
    dsimp only [a]
    exact hc.trans_le (SmallMean.A_lower hc.le hc1)
  have hratio : 0 < (1 + c) / (1 - c) :=
    div_pos (by linarith) (by linarith)
  have hz : Real.exp (-2 * a) = (1 - c) / (1 + c) := by
    dsimp only [a, SmallMean.A]
    rw [show -2 * (Real.log ((1 + c) / (1 - c)) / 2) =
        -Real.log ((1 + c) / (1 - c)) by ring,
      Real.exp_neg, Real.exp_log hratio]
    field_simp [show 1 + c ≠ 0 by linarith,
      show 1 - c ≠ 0 by linarith]
  have hra : r a = c := by
    unfold r z
    rw [hz]
    field_simp [show 1 + c ≠ 0 by linarith,
      show 1 - c ≠ 0 by linarith]
    ring
  have hcontact : (2 * x) * H v = 1 * (1 - 2 * v) := by
    dsimp only [v]
    exact radialContact_equation (by positivity) (by norm_num)
  have hxparam : E8AnalyticGerm.xParamReal c = x := by
    unfold E8AnalyticGerm.xParamReal
    rw [Correction.Natural.biasE_probability hv hv1,
      Certificates.Mixed.hn_eq_H_mul_log]
    field_simp [log_two_pos.ne', (H_pos hv hv1).ne']
    dsimp only [c]
    linear_combination -hcontact
  have hXa : X a = x := by
    rw [X_eq_xParamReal, hra, hxparam]
  refine ⟨a, ha, ?_⟩
  calc
    Y a = e8Theta (X a) := (e8Theta_X ha).symm
    _ = e8Theta x := by rw [hXa]
    _ = y := hxy

#print axioms e8SlopeRange_exists_stable_parameter

end GeneralCK

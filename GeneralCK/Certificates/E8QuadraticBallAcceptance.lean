import GeneralCK.Certificates.E8RoundedDerivativeEvaluator

/-! A rational squared-Euclidean acceptance test.  This avoids the large loss
of the previous L1 test when the output center is diagonal. -/

namespace GeneralCK.Certificates.E8QuadraticBallAcceptance

open E8ComplexBallKernel E8GaussianRatBall

def acceptsUnitSq (b : RatBall) : Bool :=
  decide (0 ≤ b.radius ∧ b.radius ≤ 1 ∧
    b.center.re ^ 2 + b.center.im ^ 2 ≤ (1 - b.radius) ^ 2)

theorem acceptsUnitSq_sound {b : RatBall} (h : acceptsUnitSq b = true)
    {z : ℂ} (hz : b.Holds z) : ‖z‖ ≤ 1 := by
  have hb : 0 ≤ b.radius ∧ b.radius ≤ 1 ∧
      b.center.re ^ 2 + b.center.im ^ 2 ≤ (1 - b.radius) ^ 2 :=
    of_decide_eq_true h
  have hr0 : (0 : ℝ) ≤ (b.radius : ℝ) := by exact_mod_cast hb.1
  have hr1 : (b.radius : ℝ) ≤ 1 := by exact_mod_cast hb.2.1
  have hsquare : ‖b.center.val‖ ^ 2 ≤ (1 - (b.radius : ℝ)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [val_re, val_im]
    have hq := hb.2.2
    simp only [pow_two] at hq ⊢
    exact_mod_cast hq
  have hcenter : ‖b.center.val‖ ≤ 1 - (b.radius : ℝ) := by nlinarith [norm_nonneg b.center.val]
  unfold RatBall.Holds InBall at hz
  calc
    ‖z‖ ≤ ‖b.center.val‖ + ‖z - b.center.val‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖b.center.val‖ + (b.radius : ℝ) := add_le_add_right hz _
    _ ≤ 1 := by linarith

end GeneralCK.Certificates.E8QuadraticBallAcceptance

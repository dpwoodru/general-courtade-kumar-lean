import GeneralCK.Certificates.E8GaussianRatBall

/-!
# Executable principal-log boxes for the E8 contact disc

This is the deliberately scoped checker used by the E8 derivative
certificate.  Given one exact rational ball for the contact coordinate, it
computes rational balls for precisely the three logarithms in `thetaParam`.
-/

namespace GeneralCK.Certificates.E8ComplexLogBoxChecker

open E8ComplexBallKernel E8GaussianRatBall

def contactRadiusQ : ℚ := 1103 / 2500
def squareRadiusQ : ℚ := contactRadiusQ ^ 2

structure LogBoxes where
  plus : RatBall
  minus : RatBall
  square : RatBall
  deriving DecidableEq, Repr

/-- Pure rational computation of the three order-12 Taylor boxes. -/
def checkLogs (c : RatBall) : LogBoxes :=
  ⟨c.logOnePlus12 contactRadiusQ,
   c.neg.logOnePlus12 contactRadiusQ,
   (c.pow 2).neg.logOnePlus12 squareRadiusQ⟩

theorem checkLogs_sound {cBall : RatBall} {c : ℂ}
    (hcBall : cBall.Holds c) (hc : ‖c‖ ≤ (contactRadiusQ : ℝ)) :
    (checkLogs cBall).plus.Holds (Complex.log (1 + c)) ∧
    (checkLogs cBall).minus.Holds (Complex.log (1 - c)) ∧
    (checkLogs cBall).square.Holds (Complex.log (1 - c ^ 2)) := by
  have hplus := holds_logOnePlus12 hcBall hc
    (by norm_num [contactRadiusQ])
  have hnegBall := holds_neg hcBall
  have hminus := holds_logOnePlus12 hnegBall (by simpa using hc)
    (by norm_num [contactRadiusQ])
  have hsqBall := holds_neg (holds_pow hcBall 2)
  have hsqNorm : ‖-(c ^ 2)‖ ≤ (squareRadiusQ : ℝ) := by
    rw [norm_neg, norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg c) hc 2
    simpa [squareRadiusQ] using h
  have hsquare := holds_logOnePlus12 hsqBall hsqNorm
    (by norm_num [squareRadiusQ, contactRadiusQ])
  simpa [checkLogs, sub_eq_add_neg] using And.intro hplus (And.intro hminus hsquare)

end GeneralCK.Certificates.E8ComplexLogBoxChecker

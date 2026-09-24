import GeneralCK.Certificates.Jet2
import GeneralCK.Certificates.E8ThetaHigherDerivatives

/-! The unconditional first/second-order bridge from the concrete `e8Q` to
the inverse recurrence. Higher orders still require derivatives of `e8Theta`. -/

namespace GeneralCK.Certificates.E8LineAnchorInverseBridge

open GeneralCK

/-- The first two derivatives of the concrete inverse, expressed in terms of
the corresponding derivatives of `e8Theta`. -/
noncomputable def e8QSecondJet : Jet2 where
  value := e8Q
  first := deriv e8Q
  second := fun y =>
    -deriv (deriv e8Theta) (e8Q y) / (deriv e8Theta (e8Q y)) ^ 3

/-- A local second derivative of `e8Theta` is the sole explicit analytic
premise. The inverse construction and both `e8Q` derivative identities are
then proved by the existing sound inverse theorems. -/
theorem e8QSecondJet_soundAt {y theta2 : ℝ} (hy : y ∈ e8SlopeRange)
    (hθ2 : HasDerivAt (deriv e8Theta) theta2 (e8Q y)) :
    e8QSecondJet.SoundAt y := by
  have hq1 := hasDerivAt_e8Q hy
  have hq2 := hasDerivAt_deriv_e8Q hy hθ2
  have hθ2eq : deriv (deriv e8Theta) (e8Q y) = theta2 := hθ2.deriv
  constructor
  · simpa [e8QSecondJet, deriv_e8Q hy] using hq1
  · simpa [e8QSecondJet, hθ2eq] using hq2

/-- The concrete second derivative recovered from the sound jet. -/
theorem deriv2_e8Q_eq_secondJet {y theta2 : ℝ} (hy : y ∈ e8SlopeRange)
    (hθ2 : HasDerivAt (deriv e8Theta) theta2 (e8Q y)) :
    deriv (deriv e8Q) y = e8QSecondJet.second y := by
  exact (e8QSecondJet_soundAt hy hθ2).2.deriv

/-- The concrete inverse jet through order two, now discharged directly from
the radial-contact formulas. -/
theorem e8QSecondJet_soundAt_unconditional {y : ℝ} (hy : y ∈ e8SlopeRange) :
    e8QSecondJet.SoundAt y := by
  exact e8QSecondJet_soundAt hy
    (GeneralCK.hasDerivAt_deriv_e8Theta (e8Q_pos hy))

/-- Unconditional identification of the concrete second derivative. -/
theorem deriv2_e8Q_eq_secondJet_unconditional {y : ℝ} (hy : y ∈ e8SlopeRange) :
    deriv (deriv e8Q) y = e8QSecondJet.second y :=
  (e8QSecondJet_soundAt_unconditional hy).2.deriv

end GeneralCK.Certificates.E8LineAnchorInverseBridge

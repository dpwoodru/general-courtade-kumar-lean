import GeneralCK.RadialDerivatives
import GeneralCK.MixedTails
import GeneralCK.Certificates.MixedCertificate

namespace GeneralCK

/-- The explicit scalar profile is bounded over its entire contact domain.
The compact part is checked from 105 original closed intervals; the tails are analytic. -/
theorem mixed_profile_global {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    Certificates.Mixed.profile v ≤ 13 / 6 := by
  by_cases hl : v ≤ 1 / 22
  · exact Certificates.Mixed.Tails.profile_left_tail hv hl
  · by_cases hr : 1 / 3 ≤ v
    · exact Certificates.Mixed.Tails.profile_right_tail hr hv'
    · exact Certificates.Mixed.mixed_compact v (le_of_not_ge hl) (le_of_not_ge hr)

/-- The manuscript's global mixed derivative bound, including both analytic tails.
Every numerical premise has been discharged by kernel-checked rational witnesses. -/
theorem global_mixed_derivative_bound {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * deriv (deriv (fun r => F r h)) z ≤ 13 / 6 := by
  rw [radius_mul_deriv2_F_eq_profile hz hh]
  exact mixed_profile_global (radialContact_pos hz hh) (radialContact_lt_half hz hh)

end GeneralCK

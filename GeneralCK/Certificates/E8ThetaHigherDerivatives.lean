import GeneralCK.PureGapE8InverseDerivatives
import GeneralCK.Certificates.MixedBounds

/-! Unconditional higher smoothness exposed from the radial-contact formulas. -/

namespace GeneralCK

open Set Filter
open Certificates.Mixed

theorem differentiableAt_profile {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    DifferentiableAt ℝ profile v := by
  have hv1 : v < 1 := by linarith
  have hk : kap v ≠ 0 := (kap_pos hv hv').ne'
  have hvc : 1-v ≠ 0 := by linarith
  have hr := ((hasDerivAt_id v).const_mul 2).const_sub 1
  have hnu := ((hasDerivAt_id v).const_mul 4).mul ((hasDerivAt_id v).const_sub 1)
  have hh := hasDerivAt_hn hv hv1
  have hk' := hasDerivAt_kap hv hv1
  have hnum := (((hr.mul (hh.pow 2)).const_mul 2).mul
    ((hk'.const_mul 2).sub (hr.pow 2)))
  have hden := ((hnu.pow 2).mul (hk'.pow 3)).const_mul (Real.log 2)
  have hd := hnum.div hden (by
    simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    exact mul_ne_zero log_two_pos.ne'
      (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num) hv.ne') hvc))
        (pow_ne_zero _ hk)))
  change DifferentiableAt ℝ
    (fun u : ℝ =>
      2*(1-2*u)*(hn u)^2*(2*kap u-(1-2*u)^2) /
        (Real.log 2*(4*u*(1-u))^2*(kap u)^3)) v
  apply hd.differentiableAt.congr_of_eventuallyEq
  filter_upwards with u
  simp only [id_eq, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.div_apply]
  ring

theorem hasDerivAt_profile {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    HasDerivAt profile (deriv profile v) v :=
  (differentiableAt_profile hv hv').hasDerivAt

/-- First derivative of `e8Theta`, rewritten through the compact radial
profile. This equality is valid on the whole positive axis. -/
theorem deriv_e8Theta_eq_profile {x : ℝ} (hx : 0 < x) :
    deriv e8Theta x = profile (radialContact (2*x) 1) / x := by
  rw [deriv_e8Theta hx]
  have hp := radius_mul_deriv2_F_eq_profile
    (z := 2*x) (h := 1) (by positivity) (by norm_num)
  have hf :
      deriv (deriv (fun r => F r 1)) (2*x) =
        profile (radialContact (2*x) 1) / (2*x) := by
    apply (eq_div_iff (by positivity : (2*x : ℝ) ≠ 0)).2
    simpa [mul_comm] using hp
  rw [hf]
  field_simp [hx.ne']

/-- Unconditional second derivative of `e8Theta`. The coefficient remains in
terms of `deriv profile`, avoiding any new analytic premise. -/
theorem hasDerivAt_deriv_e8Theta {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv e8Theta)
      ((((deriv profile (radialContact (2*x) 1) *
          (-H (radialContact (2*x) 1) /
            ((2*x) * J (radialContact (2*x) 1) + 2))) * 2) * x -
        profile (radialContact (2*x) 1)) / x^2) x := by
  let v := radialContact (2*x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1/2 := radialContact_lt_half (by positivity) (by norm_num)
  have hinner : HasDerivAt (fun u : ℝ => radialContact (2*u) 1)
      ((-H v / ((2*x)*J v+2))*2) x := by
    have hc := (hasDerivAt_radialContact_radius (z := 2*x) (h := 1)
      (by positivity) (by norm_num)).comp x ((hasDerivAt_id x).const_mul 2)
    simpa [v, Function.comp_def, mul_assoc] using hc
  have hp := (hasDerivAt_profile hv hvh).comp x hinner
  have hd := hp.div (hasDerivAt_id x) hx.ne'
  have heq : deriv e8Theta =ᶠ[nhds x]
      (profile ∘ (fun u : ℝ => radialContact (2*u) 1)) / id := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    simpa [Function.comp_def, id_eq] using deriv_e8Theta_eq_profile hu
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  dsimp only [v, id_eq, Function.comp_apply]
  ring

end GeneralCK

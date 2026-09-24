import GeneralCK.PerspectiveCurve

namespace GeneralCK
open Certificates.Mixed

/-- Contact expression for natural-unit curvature along the reflection curve.
The entropy argument `e` is in bits; `v` is the lower-half probability contact. -/
noncomputable def reflectionS (v e A b0 : ℝ) : ℝ :=
  hn v*(2*kap v-(1-2*v)^2)*(hn v+(1-2*v)*A)^2 /
    (2*(Real.log 2*e)*(4*v*(1-v))^2*(kap v)^3) +
  (1-2*v)^2*b0/((4*v*(1-v))*kap v)

set_option maxHeartbeats 1200000 in
theorem reflection_curvature_eq_contact {s e : ℝ} (hs : 0 < s) (he : 0 < e)
    (A b0 : ℝ) :
    Real.log 2 *
      ((((1/2 : ℝ)-(s/e)*(-A/(2*Real.log 2)))^2/e)*
          deriv (deriv (fun r => F r 1)) (s/e)
        +(0-(s/e)*(-b0/(2*Real.log 2)))*deriv (fun r => F r 1) (s/e)
        +(-b0/(2*Real.log 2))*F (s/e) 1) =
      reflectionS (radialContact s e) e A b0 := by
  let v := radialContact s e
  have hv : 0 < v := radialContact_pos hs he
  have hv' : v < 1/2 := radialContact_lt_half hs he
  have hr : 0 < 1-2*v := by linarith
  have hv1 : 0 < 1-v := by linarith
  have hK := (kap_pos hv hv').ne'
  have hn0 : 0 < hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_pos (H_pos hv (by linarith)) log_two_pos
  have hnz := hn0.ne'
  have heq : (s/e)*hn v = Real.log 2*(1-2*v) := by
    rw [hn_eq_H_mul_log]
    have hc := radialContact_equation hs he
    change s*H v=e*(1-2*v) at hc
    field_simp [he.ne']
    linear_combination hc
  have hratio : s/e = Real.log 2*(1-2*v)/hn v := (eq_div_iff hnz).mpr heq
  have hc : radialContact (s/e) 1 = v := (radialContact_normalize_entropy s he.ne').symm
  have hd := radius_mul_deriv2_F_eq_profile (div_pos hs he) (by norm_num : (0:ℝ)<1)
  rw [hc] at hd
  have hd' : deriv (deriv (fun r => F r 1)) (s/e) = profile v/(s/e) := by
    apply (eq_div_iff (div_pos hs he).ne').mpr
    simpa only [mul_comm] using hd
  rw [hd',deriv_F_radius_slope (div_pos hs he) (by norm_num),hc]
  have hF : F (s/e) 1 = (s/e)*J v := by rw [F,if_neg (div_pos hs he).ne',hc]
  rw [hF,hratio]
  change _ = reflectionS v e A b0
  unfold reflectionS radialSlope profile
  field_simp [log_two_pos.ne',he.ne',hnz,hK,hv.ne',hv1.ne',hr.ne']
  ring

end GeneralCK

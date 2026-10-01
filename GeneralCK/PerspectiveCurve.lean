import GeneralCK.EntropyRadialDerivatives
import GeneralCK.RadialZeroBoundary

namespace GeneralCK
open Filter Set
open scoped Topology

/-- First derivative of the homogeneous perspective along a scalar curve. -/
noncomputable def perspectiveSlope (s e ds de : ℝ) : ℝ :=
  (ds-(s/e)*de)*deriv (fun r => F r 1) (s/e)+de*F (s/e) 1

/-- The zero-radius first derivative is valid for the actual totalized function. -/
theorem hasDerivAt_F_curve_zero {s e : ℝ → ℝ} {x ds de : ℝ}
    (hs : HasDerivAt s ds x) (he : HasDerivAt e de x)
    (hs0 : s x = 0) (he0 : 0 < e x) :
    HasDerivAt (fun y => F (s y) (e y)) 0 x := by
  have hr := hs.div he he0.ne'
  have hf := (hasDerivAt_F_zero (by norm_num : (0:ℝ)<1))
  rw [← show s x/e x=0 by rw [hs0,zero_div]] at hf
  have hd := he.mul (hf.comp x hr)
  have heq : (fun y => F (s y) (e y)) =ᶠ[𝓝 x] (fun y => e y*F (s y/e y) 1) := by
    filter_upwards [he.continuousAt.eventually (Ioi_mem_nhds he0)] with y hy
    exact F_perspective (ne_of_gt hy) (s y)
  simpa [hs0,F] using hd.congr_of_eventuallyEq heq

theorem hasDerivAt_F_curve {s e : ℝ → ℝ} {x ds de : ℝ}
    (hs : HasDerivAt s ds x) (he : HasDerivAt e de x)
    (hs0 : 0 < s x) (he0 : 0 < e x) :
    HasDerivAt (fun y => F (s y) (e y)) (perspectiveSlope (s x) (e x) ds de) x := by
  have hr := hs.div he he0.ne'
  have hf := ((hasDerivAt_F_radius (div_pos hs0 he0) (by norm_num : (0:ℝ) < 1)).differentiableAt.hasDerivAt).comp x hr
  have hd := he.mul hf
  have heq : (fun y => F (s y) (e y)) =ᶠ[𝓝 x] (fun y => e y*F (s y/e y) 1) := by
    filter_upwards [he.continuousAt.eventually (Ioi_mem_nhds he0)] with y hy
    exact F_perspective (ne_of_gt hy) (s y)
  convert! hd.congr_of_eventuallyEq heq using 1
  dsimp [perspectiveSlope]
  field_simp
  ring

/-- Differentiating the explicit first derivative requires only scalar curve calculus. -/
theorem hasDerivAt_perspectiveSlope {s e ds de : ℝ → ℝ} {x dds dde : ℝ}
    (hs : HasDerivAt s (ds x) x) (he : HasDerivAt e (de x) x)
    (hds : HasDerivAt ds dds x) (hde : HasDerivAt de dde x)
    (hs0 : 0 < s x) (he0 : 0 < e x) :
    HasDerivAt (fun y => perspectiveSlope (s y) (e y) (ds y) (de y))
      (((ds x-(s x/e x)*de x)^2/e x)*deriv (deriv (fun r => F r 1)) (s x/e x)
        +(dds-(s x/e x)*dde)*deriv (fun r => F r 1) (s x/e x)
        +dde*F (s x/e x) 1) x := by
  have hr := hs.div he he0.ne'
  have hf := ((hasDerivAt_F_radius (div_pos hs0 he0) (by norm_num : (0:ℝ) < 1)).differentiableAt.hasDerivAt).comp x hr
  have hg := ((hasDerivAt_deriv_F_radius (div_pos hs0 he0) (by norm_num : (0:ℝ) < 1)).differentiableAt.hasDerivAt).comp x hr
  have hq := hds.sub (hr.mul hde)
  have hd := (hq.mul hg).add (hde.mul hf)
  convert! hd using 1
  simp only [Function.comp_apply, Pi.div_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

end GeneralCK

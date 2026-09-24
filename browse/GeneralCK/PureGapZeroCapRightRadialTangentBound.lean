import GeneralCK.RadialConvexity
import GeneralCK.RadialDerivatives
import Mathlib.Tactic.Linarith

/-! A convex supporting-line bound at a positive radial profile radius.
This source is unaudited until a direct named Lean compile. -/

namespace GeneralCK

theorem rightCap_F_supporting_tangent {r s h : ℝ}
    (hr : 0 ≤ r) (hs : 0 < s) (hh : 0 < h) :
    F s h - F r h ≤
      (s - r) * radialSlope (radialContact s h) := by
  let f : ℝ → ℝ := fun z => F z h
  have hconv : ConvexOn ℝ (Set.Ici 0) f := convexOn_F_radius hh
  have hderiv : deriv f s = radialSlope (radialContact s h) :=
    deriv_F_radius_slope hs hh
  rcases lt_trichotomy r s with hrs | heq | hsr
  · have hsec := hconv.slope_le_deriv
      (show r ∈ Set.Ici (0 : ℝ) from hr)
      (show s ∈ Set.Ici (0 : ℝ) from hs.le)
      hrs (hasDerivAt_F_radius hs hh).differentiableAt
    rw [slope_def_field, hderiv] at hsec
    have hmul := (div_le_iff₀ (sub_pos.mpr hrs)).1 hsec
    dsimp [f] at hmul
    nlinarith only [hmul]
  · subst r
    simp
  · have hsec := hconv.deriv_le_slope
      (show s ∈ Set.Ici (0 : ℝ) from hs.le)
      (show r ∈ Set.Ici (0 : ℝ) from hr)
      hsr (hasDerivAt_F_radius hs hh).differentiableAt
    rw [slope_def_field, hderiv] at hsec
    have hmul := (le_div_iff₀ (sub_pos.mpr hsr)).1 hsec
    dsimp [f] at hmul
    nlinarith only [hmul]

#print axioms rightCap_F_supporting_tangent

end GeneralCK

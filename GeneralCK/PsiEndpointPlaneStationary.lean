import GeneralCK.PsiEndpointPlaneQuotientDefs
import GeneralCK.ProfileDerivatives
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!+# Critical points of the endpoint quotient

Both first partial derivatives are proved from the concrete entropy and
Jeffreys formulas. A minimum in the open triangle therefore solves the two
logarithmic contact equations whose uniqueness is proved separately.
-/

namespace GeneralCK.PsiEndpointPlane
open Set Filter
open scoped Topology

noncomputable def ell (x : ℝ) : ℝ := Real.log 2 * J x
noncomputable def numerator (A B x y : ℝ) : ℝ :=
  naturalCost x y + A * Real.binEntropy x + B * Real.binEntropy y
noncomputable def numeratorX (A B x y : ℝ) : ℝ :=
  -(ell x - ell y) / 2 - (y - x) / (2 * x * (1 - x)) + A * ell x
noncomputable def numeratorY (A B x y : ℝ) : ℝ :=
  (ell x - ell y) / 2 + (y - x) / (2 * y * (1 - y)) + B * ell y

theorem ell_eq_logs {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ell x = Real.log (1 - x) - Real.log x := by
  unfold ell J
  rw [mul_div_cancel₀ _ log_two_pos.ne', Real.log_div (by linarith) hx.ne']

theorem naturalCost_eq_ell (x y : ℝ) :
    naturalCost x y = (y - x) * (ell x - ell y) / 2 := by
  unfold naturalCost interiorCost ell
  ring

theorem hasDerivAt_ell {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt ell (-1 / (x * (1 - x))) x := by
  convert! (hasDerivAt_J hx hx1).const_mul (Real.log 2) using 1
  field_simp [log_two_pos.ne', hx.ne', show 1 - x ≠ 0 by linarith]

theorem hasDerivAt_numerator_left {A B x y : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun z => numerator A B z y) (numeratorX A B x y) x := by
  have hc := (((hasDerivAt_id x).const_sub y).mul ((hasDerivAt_ell hx hx1).sub_const (ell y))).div_const 2
  have hh := (Real.hasDerivAt_binEntropy hx.ne' (by linarith : x ≠ 1)).const_mul A
  have h := (hc.add hh).add_const (B * Real.binEntropy y)
  convert! h using 1
  · funext z
    simp only [numerator, naturalCost_eq_ell, Pi.add_apply, Pi.mul_apply, id_eq]
  · dsimp [numeratorX]
    rw [ell_eq_logs hx hx1]
    field_simp
    ring

theorem hasDerivAt_numerator_right {A B x y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun z => numerator A B x z) (numeratorY A B x y) y := by
  have hc := (((hasDerivAt_id y).sub_const x).mul ((hasDerivAt_ell hy hy1).const_sub (ell x))).div_const 2
  have hh := (Real.hasDerivAt_binEntropy hy.ne' (by linarith : y ≠ 1)).const_mul B
  have h := (hc.add_const (A * Real.binEntropy x)).add hh
  convert! h using 1
  · funext z
    simp only [numerator, naturalCost_eq_ell, Pi.add_apply, Pi.mul_apply, id_eq]
  · dsimp [numeratorY]
    rw [ell_eq_logs hy hy1]
    field_simp

theorem hasDerivAt_quotient_left {A B x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy1 : y < 1) :
    HasDerivAt (fun z => quotient A B z y)
      ((numeratorX A B x y * (y - x) + numerator A B x y) / (y - x) ^ 2) x := by
  convert! (hasDerivAt_numerator_left hx (hxy.trans hy1)).div
    ((hasDerivAt_id x).const_sub y) (sub_pos.mpr hxy).ne' using 1
  dsimp
  ring

theorem hasDerivAt_quotient_right {A B x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy1 : y < 1) :
    HasDerivAt (fun z => quotient A B x z)
      ((numeratorY A B x y * (y - x) - numerator A B x y) / (y - x) ^ 2) y := by
  convert! (hasDerivAt_numerator_right (hx.trans hxy) hy1).div
    ((hasDerivAt_id y).sub_const x) (sub_pos.mpr hxy).ne' using 1
  dsimp
  ring

theorem contactLevel0_identity {A B x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy1 : y < 1) :
    contactLevel0 A B x y =
      x * numeratorX A B x y + y * numeratorY A B x y - numerator A B x y := by
  have hx1 := hxy.trans hy1
  have hy := hx.trans hxy
  unfold contactLevel0 numeratorX numeratorY numerator
  rw [naturalCost_eq_ell, ell_eq_logs hx hx1, ell_eq_logs hy hy1]
  simp only [Real.binEntropy, Real.log_inv]
  field_simp [hx.ne', hy.ne', show 1 - x ≠ 0 by linarith, show 1 - y ≠ 0 by linarith]
  ring

theorem contactLevel1_identity {A B x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy1 : y < 1) :
    contactLevel1 A B x y = -numerator A B x y -
      (1 - x) * numeratorX A B x y - (1 - y) * numeratorY A B x y := by
  have hx1 := hxy.trans hy1
  have hy := hx.trans hxy
  unfold contactLevel1 numeratorX numeratorY numerator
  rw [naturalCost_eq_ell, ell_eq_logs hx hx1, ell_eq_logs hy hy1]
  simp only [Real.binEntropy, Real.log_inv]
  field_simp [hx.ne', hy.ne', show 1 - x ≠ 0 by linarith, show 1 - y ≠ 0 by linarith]
  ring

/-- Both zero partial derivatives force the two concrete contact equations. -/
theorem contactLevels_zero_of_stationary {A B x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy1 : y < 1)
    (hleft : deriv (fun z => quotient A B z y) x = 0)
    (hright : deriv (fun z => quotient A B x z) y = 0) :
    contactLevel1 A B x y = 0 ∧ contactLevel0 A B x y = 0 := by
  rw [(hasDerivAt_quotient_left hx hxy hy1).deriv] at hleft
  rw [(hasDerivAt_quotient_right hx hxy hy1).deriv] at hright
  have hn := pow_ne_zero 2 (sub_pos.mpr hxy).ne'
  have hl := (div_eq_zero_iff).mp hleft
  have hr := (div_eq_zero_iff).mp hright
  simp only [hn, or_false] at hl hr
  have hs : numeratorX A B x y + numeratorY A B x y = 0 := by
    have hmul : (y - x) * (numeratorX A B x y + numeratorY A B x y) = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left (sub_pos.mpr hxy).ne'
  rw [contactLevel1_identity hx hxy hy1, contactLevel0_identity hx hxy hy1]
  constructor
  · linear_combination (x - 1) * hs + hr
  · linear_combination x * hs + hr

theorem contactLevels_zero_of_minimum {A B x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy1 : y < 1)
    (hmin : ∀ u v : ℝ, 0 < u → u < v → v < 1 → quotient A B x y ≤ quotient A B u v) :
    contactLevel1 A B x y = 0 ∧ contactLevel0 A B x y = 0 := by
  apply contactLevels_zero_of_stationary hx hxy hy1
  · have hm : IsLocalMin (fun z => quotient A B z y) x := by
      filter_upwards [Ioo_mem_nhds hx hxy] with z hz
      exact hmin z y hz.1 hz.2 hy1
    exact hm.deriv_eq_zero
  · have hm : IsLocalMin (fun z => quotient A B x z) y := by
      filter_upwards [Ioo_mem_nhds hxy hy1] with z hz
      exact hmin x z hx hz.1 hz.2
    exact hm.deriv_eq_zero

end GeneralCK.PsiEndpointPlane

#print axioms GeneralCK.PsiEndpointPlane.contactLevels_zero_of_minimum

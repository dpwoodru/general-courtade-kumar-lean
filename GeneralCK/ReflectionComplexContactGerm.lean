import GeneralCK.ReflectionComplexFixedPoint
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Holomorphic germ of the complex contact point

Near zero, the contact equation can be inverted in one complex variable:
`tau = c / entropyExt c`.  This gives a holomorphic germ directly from the
analytic inverse-function theorem and identifies it locally with the Banach
fixed point constructed on the quantitative disc.
-/

namespace GeneralCK.Reflection.ComplexContactGerm

open Set Filter Function
open scoped Topology
open ComplexEntropy ComplexFixedPoint

/-- The principal-log entropy is analytic at every point of the open unit
disc. -/
theorem analyticAt_entropyExt {c : ℂ} (hc : ‖c‖ < 1) :
    AnalyticAt ℂ entropyExt c := by
  have hp : AnalyticAt ℂ (fun z : ℂ => 1 + z) c :=
    analyticAt_const.add analyticAt_id
  have hm : AnalyticAt ℂ (fun z : ℂ => 1 - z) c :=
    analyticAt_const.sub analyticAt_id
  have hpSlit : 1 + c ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_of_norm_lt_one hc
  have hmSlit : 1 - c ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg, norm_neg] using
      (Complex.mem_slitPlane_of_norm_lt_one (z := -c) (by simpa using hc))
  unfold entropyExt
  exact analyticAt_const.sub
    (((hp.mul (hp.clog hpSlit)).add (hm.mul (hm.clog hmSlit))).div
      analyticAt_const (by norm_num))

@[simp] theorem entropyExt_zero : entropyExt 0 = (Real.log 2 : ℂ) := by
  simp [entropyExt]

private theorem entropyExt_zero_ne : entropyExt 0 ≠ 0 := by
  rw [entropyExt_zero]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

/-- The analytic map whose local inverse is the contact point. -/
noncomputable def slopeMap (c : ℂ) : ℂ := c / entropyExt c

@[simp] theorem slopeMap_zero : slopeMap 0 = 0 := by simp [slopeMap]

theorem analyticAt_slopeMap : AnalyticAt ℂ slopeMap 0 := by
  unfold slopeMap
  exact analyticAt_id.div (analyticAt_entropyExt (by norm_num)) entropyExt_zero_ne

/-- Exact derivative of the reciprocal-slope map at the origin. -/
theorem hasDerivAt_slopeMap_zero :
    HasDerivAt slopeMap (Real.log 2 : ℂ)⁻¹ 0 := by
  have h := (hasDerivAt_id (𝕜 := ℂ) 0).div
    (hasDerivAt_entropyExt (by norm_num)) entropyExt_zero_ne
  have h' : (Real.log 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  have hcoef :
      ((1 : ℂ) * entropyExt 0 - 0 * entropyDeriv 0) / entropyExt 0 ^ 2 =
        (Real.log 2 : ℂ)⁻¹ := by
    rw [entropyExt_zero]
    simp only [one_mul, zero_mul, sub_zero]
    field_simp [h']
  rw [show slopeMap = id / entropyExt by rfl, ← hcoef]
  simpa only [id_eq] using h

private theorem deriv_slopeMap_zero : deriv slopeMap 0 = (Real.log 2 : ℂ)⁻¹ :=
  hasDerivAt_slopeMap_zero.deriv

private theorem deriv_slopeMap_ne : deriv slopeMap 0 ≠ 0 := by
  rw [deriv_slopeMap_zero]
  exact inv_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num))))

/-- The holomorphic contact germ at `tau = 0`, obtained as the local inverse
of `c ↦ c / entropyExt c`. -/
noncomputable def contactGerm : ℂ → ℂ :=
  analyticAt_slopeMap.hasStrictDerivAt.localInverse slopeMap
    (deriv slopeMap 0) 0 deriv_slopeMap_ne

@[simp] theorem contactGerm_zero : contactGerm 0 = 0 := by
  have h := analyticAt_slopeMap.hasStrictDerivAt.eventually_left_inverse
    deriv_slopeMap_ne
  simpa [contactGerm] using h.self_of_nhds

/-- The contact germ is genuinely complex analytic at the origin. -/
theorem analyticAt_contactGerm : AnalyticAt ℂ contactGerm 0 := by
  simpa [contactGerm] using
    analyticAt_slopeMap.analyticAt_localInverse deriv_slopeMap_ne

/-- Its linear coefficient is `log 2`. -/
theorem hasDerivAt_contactGerm_zero :
    HasDerivAt contactGerm (Real.log 2 : ℂ) 0 := by
  have h := analyticAt_slopeMap.hasStrictDerivAt.to_localInverse deriv_slopeMap_ne
  simpa [contactGerm, deriv_slopeMap_zero] using h.hasDerivAt

/-- Reusable derivative formula for any differentiable local solution of the
complex contact equation. -/
theorem contact_deriv_eq {phi : ℂ → ℂ} {tau phi' : ℂ}
    (hphi : HasDerivAt phi phi' tau)
    (hdisc : ‖phi tau‖ < 1)
    (heq : phi =ᶠ[𝓝 tau] fun z => z * entropyExt (phi z))
    (hden : 1 - tau * entropyDeriv (phi tau) ≠ 0) :
    phi' = entropyExt (phi tau) /
      (1 - tau * entropyDeriv (phi tau)) := by
  have hEntropy := (hasDerivAt_entropyExt hdisc).comp tau hphi
  have hRight := (hasDerivAt_id tau).mul hEntropy
  have hRight' : HasDerivAt phi
      (1 * entropyExt (phi tau) + tau * (entropyDeriv (phi tau) * phi')) tau :=
    hRight.congr_of_eventuallyEq heq
  have hd := hphi.unique hRight'
  apply (eq_div_iff hden).2
  calc
    phi' * (1 - tau * entropyDeriv (phi tau)) =
        phi' - tau * (entropyDeriv (phi tau) * phi') := by ring
    _ = entropyExt (phi tau) := by
      nth_rw 1 [hd]
      ring

/-- Locally, the germ satisfies the exact complex entropy contact equation. -/
theorem eventually_contactGerm_fixed :
    ∀ᶠ tau in 𝓝 (0 : ℂ),
      contactGerm tau = tau * entropyExt (contactGerm tau) := by
  have hinv := analyticAt_slopeMap.hasStrictDerivAt.eventually_right_inverse
    deriv_slopeMap_ne
  simp only [slopeMap_zero] at hinv
  have hcont : ContinuousAt (fun tau => entropyExt (contactGerm tau)) 0 :=
    (analyticAt_entropyExt (c := 0) (by norm_num)).continuousAt.comp_of_eq
      analyticAt_contactGerm.continuousAt contactGerm_zero
  have hne : ∀ᶠ tau in 𝓝 (0 : ℂ), entropyExt (contactGerm tau) ≠ 0 := by
    apply hcont.eventually_ne
    simpa only [contactGerm_zero] using entropyExt_zero_ne
  filter_upwards [hinv, hne] with tau htau hE
  unfold slopeMap at htau
  exact (div_eq_iff hE).mp htau

/-- In a neighborhood of zero the holomorphic germ stays in the open
`4/5` contact disc. -/
theorem eventually_contactGerm_mem_ball :
    ∀ᶠ tau in 𝓝 (0 : ℂ), contactGerm tau ∈ Metric.ball 0 (4 / 5 : ℝ) := by
  apply analyticAt_contactGerm.continuousAt
  simpa using Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 4 / 5)

/-- Local compatibility with the quantitatively constructed Banach fixed
point.  The conclusion is independent of the proof of the norm bound. -/
theorem eventually_contactGerm_eq_fixedPoint :
    ∀ᶠ tau in 𝓝 (0 : ℂ), ∀ htau : ‖tau‖ ≤ (7 / 10 : ℝ),
      contactGerm tau = fixedPoint tau htau := by
  filter_upwards [eventually_contactGerm_fixed, eventually_contactGerm_mem_ball]
    with tau hfix hmem
  intro htau
  apply eq_fixedPoint htau (Metric.ball_subset_closedBall hmem)
  exact hfix.symm

end GeneralCK.Reflection.ComplexContactGerm

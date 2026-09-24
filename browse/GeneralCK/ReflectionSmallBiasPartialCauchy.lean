import GeneralCK.ReflectionSmallBiasRemainder
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Cauchy bounds for the mixed derivative of the reflection remainder -/

namespace GeneralCK.Reflection.SmallBiasPartialCauchy

open Set Filter
open scoped Topology

noncomputable def partialA (f : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  fderiv ℂ f p (1, 0)

noncomputable def partialAA (f : ℂ × ℂ → ℂ) : ℂ × ℂ → ℂ := partialA (partialA f)

theorem analyticAt_partialA {f : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hf : AnalyticAt ℂ f p) : AnalyticAt ℂ (partialA f) p := by
  unfold partialA
  exact ((ContinuousLinearMap.apply ℂ ℂ ((1, 0) : ℂ × ℂ)).analyticAt _).comp hf.fderiv

theorem analyticAt_partialAA {f : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hf : AnalyticAt ℂ f p) : AnalyticAt ℂ (partialAA f) p :=
  analyticAt_partialA (analyticAt_partialA hf)

theorem hasDerivAt_sliceA {f : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hf : AnalyticAt ℂ f p) :
    @HasDerivAt ℂ _ ℂ _
      (((NormedAlgebra.toNormedSpace ℂ) : NormedSpace ℂ ℂ).toModule) _ _
      (fun z : ℂ => f (z, p.2)) (partialA f p) p.1 := by
  have hh := hf.differentiableAt.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  simpa only [Function.comp_def, id_eq, partialA] using hh

theorem partialAA_eq_deriv2 {f : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hf : AnalyticAt ℂ f p) :
    partialAA f p = deriv (deriv (fun z : ℂ => f (z, p.2))) p.1 := by
  have hp : Tendsto (fun z : ℂ => (z, p.2)) (𝓝 p.1) (𝓝 p) :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto
  have he : (fun z : ℂ => partialA f (z, p.2)) =ᶠ[𝓝 p.1]
      deriv (fun z : ℂ => f (z, p.2)) := by
    filter_upwards [hp.eventually hf.eventually_analyticAt] with z hz
    exact (hasDerivAt_sliceA hz).deriv.symm
  exact (hasDerivAt_sliceA (analyticAt_partialA hf)).deriv.symm.trans he.deriv_eq

theorem norm_partialAA_le {f : ℂ × ℂ → ℂ} {a b : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hf : ∀ z ∈ Metric.closedBall a r, AnalyticAt ℂ f (z, b))
    (hb : ∀ z ∈ Metric.sphere a r, ‖f (z, b)‖ ≤ M) :
    ‖partialAA f (a, b)‖ ≤ 2 * M / r ^ 2 := by
  have ha : a ∈ Metric.closedBall a r := Metric.mem_closedBall_self hr.le
  rw [partialAA_eq_deriv2 (hf a ha)]
  apply SmallBiasRemainder.norm_deriv2_le hr
  · apply DifferentiableOn.diffContOnCl_ball _ subset_rfl
    intro z hz
    exact (hasDerivAt_sliceA (hf z hz)).differentiableAt.differentiableWithinAt
  · exact hb

/-- Two derivatives in the first variable and one in the second cost `2/r^3`
when the function is bounded on the corresponding closed bidisc. -/
theorem norm_deriv_partialAA_le {f : ℂ × ℂ → ℂ} {a b : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hf : ∀ z ∈ Metric.closedBall a r, ∀ w ∈ Metric.closedBall b r,
      AnalyticAt ℂ f (z, w))
    (hb : ∀ z ∈ Metric.closedBall a r, ∀ w ∈ Metric.closedBall b r,
      ‖f (z, w)‖ ≤ M) :
    ‖deriv (fun w : ℂ => partialAA f (a, w)) b‖ ≤ 2 * M / r ^ 3 := by
  have ha : a ∈ Metric.closedBall a r := Metric.mem_closedBall_self hr.le
  have hd : DiffContOnCl ℂ (fun w : ℂ => partialAA f (a, w)) (Metric.ball b r) := by
    apply DifferentiableOn.diffContOnCl_ball _ subset_rfl
    intro w hw
    have hh := (analyticAt_partialAA (hf a ha w hw)).comp
      (analyticAt_const.prod analyticAt_id : AnalyticAt ℂ (fun v : ℂ => (a, v)) w)
    exact hh.differentiableAt.differentiableWithinAt
  have hn : ∀ w ∈ Metric.sphere b r, ‖partialAA f (a, w)‖ ≤ 2 * M / r ^ 2 := by
    intro w hw
    have hw' := Metric.sphere_subset_closedBall hw
    exact norm_partialAA_le hr (fun z hz => hf z hz w hw')
      (fun z hz => hb z (Metric.sphere_subset_closedBall hz) w hw')
  calc
    _ ≤ (2 * M / r ^ 2) / r :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd hn
    _ = 2 * M / r ^ 3 := by ring

end GeneralCK.Reflection.SmallBiasPartialCauchy

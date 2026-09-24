import GeneralCK.ReflectionSmallBiasJetConstructors

/-! # The geometric-series remainder for Taylor-jet inversion -/

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open Filter Asymptotics SmallBiasPolynomial
open scoped Topology

theorem inverse_one_sub {n : ℕ} {k : ℂ} {f : ℂ × ℂ → ℂ} {p : List Term}
    (hk : k ≠ 0) (hf : Approximates n k f p) (hzero : f 0 = 0) :
    Approximates n k (fun z => (1 - f z)⁻¹) (SmallBiasPolynomial.geometric n p) := by
  have ha : AnalyticAt ℂ (fun z => (1 - f z)⁻¹) 0 :=
    (analyticAt_const.sub hf.analytic).inv (by simp [hzero])
  have hb : (fun z => (1 - f z)⁻¹) =O[𝓝 (0 : ℂ × ℂ)] (fun _ => (1 : ℝ)) :=
    ha.continuousAt.tendsto.isBigO_one ℝ
  have hp := (hf.function_isBigO_norm hzero).pow n
  have he : (fun z => f z ^ n * (1 - f z)⁻¹)
      =O[𝓝 (0 : ℂ × ℂ)] (fun z => ‖z‖ ^ n) := by
    simpa only [mul_one] using hp.mul hb
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), 1 - f z ≠ 0 :=
    (continuousAt_const.sub hf.analytic.continuousAt).eventually_ne (by simp [hzero])
  have heq : (fun z => f z ^ n * (1 - f z)⁻¹) =ᶠ[𝓝 (0 : ℂ × ℂ)]
      (fun z => (1 - f z)⁻¹ - ∑ j ∈ Finset.range n, f z ^ j) := by
    filter_upwards [hne] with z hz
    calc
      _ = (1 - (∑ j ∈ Finset.range n, f z ^ j) * (1 - f z)) / (1 - f z) := by
        rw [geom_sum_mul_neg]
        ring
      _ = (1 - f z)⁻¹ - ∑ j ∈ Finset.range n, f z ^ j := by
        field_simp [hz]
  exact (hf.geometric hk).transfer ha (he.congr' heq Filter.EventuallyEq.rfl)

end GeneralCK.Reflection.SmallBiasJet.Approximates

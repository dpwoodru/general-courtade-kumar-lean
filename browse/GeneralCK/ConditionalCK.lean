import GeneralCK.EntropyFlow
import GeneralCK.LimitTransfer

namespace GeneralCK
open scoped BigOperators

theorem regularizedEntropyBound_of_bellman (hB : FiniteHybridBellman) :
    LimitTransfer.RegularizedEntropyBound := by
  intro n f eps p he he' hp hp'
  let T : ℝ := -Real.log (1 - 2 * p) / 2
  have harg : 0 < 1 - 2 * p := by linarith
  have harg' : 1 - 2 * p ≤ 1 := by linarith
  have hT : 0 ≤ T := by
    have hlog := Real.log_nonpos harg.le harg'
    dsimp [T]
    linarith
  have hexp : Real.exp (-2 * T) = 1 - 2 * p := by
    have h : -2 * T = Real.log (1 - 2 * p) := by dsimp [T]; ring
    rw [h, Real.exp_log harg]
  have hcross : Noise.crossover T = p := by unfold Noise.crossover; rw [hexp]; ring
  have hparam : Comparison.noiseParameter eps T = eps + p - 2 * eps * p := by
    unfold Comparison.noiseParameter
    rw [hexp]
    ring
  have hflow : Flow.flow f eps T = LimitTransfer.regularizedPosterior f p eps := by
    funext x
    unfold Flow.flow Flow.regularized LimitTransfer.regularizedPosterior
    rw [hcross, Noise.applyNoise_affine, Noise.applyNoise_indicator]
  have h := Flow.entropy_flow_bound hB f he he' hT
  rw [hparam] at h
  simpa only [Flow.delta, Flow.gamma, Flow.initialMean_eq, hflow,
    CubeAnalysis.mean, Information.cubeWeight, LimitTransfer.regularizedMean,
    Function.comp_apply] using h

/-- Complete conditional deduction: the precise finite hybrid Bellman
inequality implies the approved general CK theorem, including every endpoint.
The Bellman premise itself remains to be proved. -/
theorem generalCourtadeKumar_of_finiteHybridBellman
    (hB : FiniteHybridBellman) : GeneralCourtadeKumar :=
  LimitTransfer.regularizedEntropyBound_implies_CK (regularizedEntropyBound_of_bellman hB)

theorem bellmanToCK : BellmanToCK := generalCourtadeKumar_of_finiteHybridBellman

end GeneralCK

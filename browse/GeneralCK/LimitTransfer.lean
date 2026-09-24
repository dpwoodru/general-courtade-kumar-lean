import GeneralCK.Regularization

namespace GeneralCK.LimitTransfer
open scoped BigOperators

noncomputable def regularizedPosterior {n : ℕ} (f : Cube n → Bool) (p eps : ℝ)
    (y : Cube n) : ℝ := eps + (1 - 2 * eps) * Information.posterior f p y

noncomputable def regularizedMean {n : ℕ} (f : Cube n → Bool) (eps : ℝ) : ℝ :=
  eps + (1 - 2 * eps) * Information.meanIndicator f

def RegularizedEntropyBound : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (eps p : ℝ),
    0 < eps → eps < 1 / 2 → 0 < p → p < 1 / 2 →
      H (eps + p - 2 * eps * p) ≤
        Information.cubeWeight n * (∑ y, H (regularizedPosterior f p eps y)) +
          1 - H (regularizedMean f eps)

theorem regularizedEntropyBound_implies_CK (hBound : RegularizedEntropyBound) :
    GeneralCourtadeKumar := by
  apply Regularization.CK_of_open_lower_half
  intro n f p hp hp'
  have hleft : Continuous (fun eps : ℝ => H (eps + p - 2 * eps * p)) := by
    apply H_continuous.comp
    fun_prop
  have hright : Continuous (fun eps : ℝ =>
      Information.cubeWeight n * (∑ y, H (regularizedPosterior f p eps y)) +
        1 - H (regularizedMean f eps)) := by
    apply Continuous.sub
    · apply Continuous.add _ continuous_const
      apply Continuous.const_mul
      apply continuous_finsetSum
      intro y _
      apply H_continuous.comp
      unfold regularizedPosterior
      fun_prop
    · apply H_continuous.comp
      unfold regularizedMean
      fun_prop
  have hz : (0 : ℝ) ∈ closure (Set.Ioo 0 (1 / 2 : ℝ)) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2)]
    exact ⟨le_rfl, by norm_num⟩
  have hlim := ContinuousWithinAt.closure_le hz hleft.continuousAt.continuousWithinAt
    hright.continuousAt.continuousWithinAt
    (fun eps heps => hBound n f eps p heps.1 heps.2 hp hp')
  simp only [regularizedPosterior, regularizedMean, mul_zero, zero_mul, sub_zero,
    one_mul, zero_add] at hlim
  rw [Information.mutualInformation_eq]
  linarith

end GeneralCK.LimitTransfer

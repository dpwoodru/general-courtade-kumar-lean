import GeneralCK.CorrectionHessianPSD

namespace GeneralCK.Correction

/-- Natural-log entropy slope, rather than the bit-entropy slope `J`. -/
noncomputable def naturalJ (f : ℝ) : ℝ := Real.log 2 * J (entropyInverse f)

noncomputable def rankWeight (e f : ℝ) : ℝ :=
  2 * Real.log 2 * deriv (deriv (fun r => F r (mid e f))) (gap e f)

/-- Numerator of `Aright`; this expression has no division by `naturalJ f`. -/
noncomputable def rightNumerator (e f : ℝ) : ℝ :=
  q f * (naturalJ e + naturalJ f -
    2 * Real.log 2 * deriv (fun r => F r 1) (normalized e f)) +
  gap e f * (1 - naturalJ f * (1 - 2 * entropyInverse f))

/-- Denominator-cleared determinant with the quadratic rank-one terms cancelled. -/
noncomputable def Kfactored (e f : ℝ) : ℝ :=
  Aleft e f * rightNumerator e f - naturalJ f * (q e + q f)^2 -
  rankWeight e f * (naturalJ f * Aleft e f * (Zright e f)^2 +
    rightNumerator e f * (Zleft e f)^2 +
    2 * naturalJ f * (q e + q f) * Zleft e f * Zright e f)

theorem Mdet_rank_one (e f : ℝ) :
    Mdet e f = Aleft e f * Aright e f - (q e + q f)^2 -
      rankWeight e f * (Aleft e f * (Zright e f)^2 +
        Aright e f * (Zleft e f)^2 +
        2 * (q e + q f) * Zleft e f * Zright e f) := by
  unfold Mdet Mleft Mright Mcross rankWeight
  ring

theorem naturalJ_pos {f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    0 < naturalJ f :=
  mul_pos log_two_pos (J_pos (entropyInverse_pos hf hf'.le)
    (entropyInverse_lt_half hf.le hf'))

theorem Aright_eq_numerator (e f : ℝ) :
    Aright e f = rightNumerator e f / naturalJ f := rfl

theorem naturalJ_mul_Aright {e f : ℝ} (hJ : naturalJ f ≠ 0) :
    naturalJ f * Aright e f = rightNumerator e f := by
  rw [Aright_eq_numerator]
  exact mul_div_cancel₀ _ hJ

/-- The nonzero slope hypothesis is essential when clearing the right denominator. -/
theorem Kfactored_eq_mul_Mdet {e f : ℝ} (hJ : naturalJ f ≠ 0) :
    Kfactored e f = naturalJ f * Mdet e f := by
  rw [Mdet_rank_one]
  unfold Kfactored
  linear_combination
    (rankWeight e f * (Zleft e f)^2 - Aleft e f) *
      (naturalJ_mul_Aright (e := e) hJ)

theorem Kfactored_eq_mul_Mdet_interior {e f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    Kfactored e f = naturalJ f * Mdet e f :=
  Kfactored_eq_mul_Mdet (naturalJ_pos hf hf').ne'

theorem Mdet_pos_iff_Kfactored_pos {e f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    0 < Mdet e f ↔ 0 < Kfactored e f := by
  rw [Kfactored_eq_mul_Mdet_interior hf hf']
  exact (mul_pos_iff_of_pos_left (naturalJ_pos hf hf')).symm

theorem Mdet_nonneg_iff_Kfactored_nonneg {e f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    0 ≤ Mdet e f ↔ 0 ≤ Kfactored e f := by
  rw [Kfactored_eq_mul_Mdet_interior hf hf']
  exact (mul_nonneg_iff_of_pos_left (naturalJ_pos hf hf')).symm

end GeneralCK.Correction

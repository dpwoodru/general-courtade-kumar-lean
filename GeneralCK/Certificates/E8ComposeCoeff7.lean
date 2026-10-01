import GeneralCK.Certificates.E8ThetaParamCoeff5
import GeneralCK.Certificates.E8HigherRationalTrace

namespace GeneralCK.Certificates.E8ComposeCoeff7

open E8AnalyticGerm E8AnalyticInverseRecurrence E8HigherSourceBoxBridge
open E8HigherRationalTrace E8ThetaParamCoeff5 E8LowOrderThetaCoefficients

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
private theorem clogTwo_eq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
  (Complex.natCast_log (n := 2)).symm

theorem powCoeff_zero_of_lt (b : ℕ → ℂ) (b0 : b 0 = 0) :
    ∀ k n, n < k → powCoeff b k n = 0 := by
  intro k
  induction k with
  | zero => intro n h; omega
  | succ k ih =>
      intro n hn
      simp only [powCoeff]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hi0 : i = 0
      · subst i; simp [b0]
      · have hil : i ≤ n := by simpa using Finset.mem_range.mp hi
        have hlt : n - i < k := by omega
        rw [ih (n - i) hlt]
        simp

theorem powCoeff_diag (b : ℕ → ℂ) (b0 : b 0 = 0) :
    ∀ k, powCoeff b k k = b 1 ^ k := by
  intro k
  induction k with
  | zero => simp [powCoeff]
  | succ k ih =>
      simp only [powCoeff]
      rw [Finset.sum_eq_single 1]
      · simp [ih]
        ring
      · intro i hi hi1
        by_cases hi0 : i = 0
        · subst i; simp [b0]
        · have hil : i ≤ k + 1 := by simpa using Finset.mem_range.mp hi
          have hlt : k + 1 - i < k := by omega
          rw [powCoeff_zero_of_lt b b0 k (k + 1 - i) hlt]
          simp
      · simp

theorem powCoeff_next_diag_zero (b : ℕ → ℂ) (b0 : b 0 = 0)
    (b2 : b 2 = 0) : ∀ k, powCoeff b k (k + 1) = 0 := by
  intro k
  induction k with
  | zero => simp [powCoeff]
  | succ k ih =>
      simp only [powCoeff]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hi0 : i = 0
      · subst i; simp [b0]
      by_cases hi1 : i = 1
      · subst i
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          congrArg (fun z => b 1 * z) ih
      by_cases hi2 : i = 2
      · subst i; simp [b2]
      · have hil : i ≤ k + 2 := by simpa using Finset.mem_range.mp hi
        have hlt : k + 2 - i < k := by omega
        rw [powCoeff_zero_of_lt b b0 k (k + 2 - i) hlt]
        simp

private theorem powCoeff_two_seven_odd (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) (b6 : b 6 = 0) :
    powCoeff b 2 7 = 0 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6, powCoeff_zero_of_lt]

private theorem powCoeff_three_seven_odd (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) (b6 : b 6 = 0) :
    powCoeff b 3 7 = 3*b 1^2*b 5 + 3*b 1*b 3^2 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6, powCoeff_zero_of_lt]
  ring

private theorem powCoeff_four_seven_odd (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) (b6 : b 6 = 0) :
    powCoeff b 4 7 = 0 := by
  simp [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6]

set_option maxHeartbeats 0 in
private theorem powCoeff_five_seven_odd (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) (b6 : b 6 = 0) :
    powCoeff b 5 7 = 5*b 1^4*b 3 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6]
  ring

private theorem powCoeff_six_seven_odd (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) (b6 : b 6 = 0) :
    powCoeff b 6 7 = 0 := by
  simpa using powCoeff_next_diag_zero b b0 b2 6

private theorem powCoeff_seven_seven_odd (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) (b6 : b 6 = 0) :
    powCoeff b 7 7 = b 1^7 := powCoeff_diag b b0 7

theorem composeCoeff_seven_odd (a b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) (b6 : b 6 = 0) :
    composeCoeff a b 7 = a 1 * b 7 +
      a 3 * (3 * b 1 ^ 2 * b 5 + 3 * b 1 * b 3 ^ 2) +
      a 5 * (5 * b 1 ^ 4 * b 3) + a 7 * b 1 ^ 7 := by
  simp only [composeCoeff, Finset.sum_range_succ]
  rw [powCoeff_one,
    powCoeff_two_seven_odd b b0 b2 b4 b6,
    powCoeff_three_seven_odd b b0 b2 b4 b6,
    powCoeff_four_seven_odd b b0 b2 b4 b6,
    powCoeff_five_seven_odd b b0 b2 b4 b6,
    powCoeff_six_seven_odd b b0 b2 b4 b6,
    powCoeff_seven_seven_odd b b0 b2 b4 b6]
  simp [powCoeff]

end GeneralCK.Certificates.E8ComposeCoeff7


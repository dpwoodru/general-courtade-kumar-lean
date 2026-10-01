import GeneralCK.Certificates.E8ComposeCoeff7

namespace GeneralCK.Certificates.E8ComposeCoeff9

open E8AnalyticInverseRecurrence E8ComposeCoeff7

private theorem powCoeff_two_four (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 2 4 = 2 * b 1 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_one]
  ring

private theorem powCoeff_three_five (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 3 5 = 3 * b 1 ^ 2 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_two_four,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

private theorem powCoeff_four_six (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 4 6 = 4 * b 1 ^ 3 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_three_five,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

private theorem powCoeff_five_seven (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 5 7 = 5 * b 1 ^ 4 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_four_six,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

private theorem powCoeff_six_eight (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 6 8 = 6 * b 1 ^ 5 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_five_seven,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

private theorem powCoeff_seven_nine (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 7 9 = 7 * b 1 ^ 6 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_six_eight,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

private theorem powCoeff_three_nine_odd (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    powCoeff b 3 9 = 3*b 1^2*b 7 + 6*b 1*b 3*b 5 + b 3^3 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6, b8]
  ring

set_option maxHeartbeats 0 in
private theorem powCoeff_five_nine_odd (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    powCoeff b 5 9 = 5*b 1^4*b 5 + 10*b 1^3*b 3^2 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6, b8]
  ring

theorem composeCoeff_nine_odd (a b : ℕ → ℂ)
    (a2 : a 2 = 0) (a4 : a 4 = 0) (a6 : a 6 = 0)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    composeCoeff a b 9 = a 1*b 9 +
      a 3*(3*b 1^2*b 7 + 6*b 1*b 3*b 5 + b 3^3) +
      a 5*(5*b 1^4*b 5 + 10*b 1^3*b 3^2) +
      a 7*(7*b 1^6*b 3) + a 9*b 1^9 := by
  simp only [composeCoeff, Finset.sum_range_succ]
  rw [a2, a4, a6]
  simp only [zero_mul, add_zero]
  rw [powCoeff_one,
    powCoeff_three_nine_odd b b0 b2 b4 b6 b8,
    powCoeff_five_nine_odd b b0 b2 b4 b6 b8,
    powCoeff_seven_nine b b0 b2,
    powCoeff_next_diag_zero b b0 b2 8,
    powCoeff_diag b b0 9]
  simp [powCoeff, b0]

end GeneralCK.Certificates.E8ComposeCoeff9

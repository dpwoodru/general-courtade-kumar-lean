import GeneralCK.Certificates.E8ComposeCoeff9

namespace GeneralCK.Certificates.E8ComposeCoeff11

open E8AnalyticInverseRecurrence E8ComposeCoeff7

theorem p3_5 (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 3 5 = 3 * b 1 ^ 2 * b 3 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, powCoeff_zero_of_lt]
  ring

theorem p4_6 (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 4 6 = 4 * b 1 ^ 3 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, p3_5, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p5_7 (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 5 7 = 5 * b 1 ^ 4 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, p4_6, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p6_8 (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 6 8 = 6 * b 1 ^ 5 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, p5_7, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p7_9 (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 7 9 = 7 * b 1 ^ 6 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, p6_8, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p8_10 (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 8 10 = 8 * b 1 ^ 7 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, p7_9, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p9_11 (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 9 11 = 9 * b 1 ^ 8 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, p8_10, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p3_7 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 3 7 = 3 * b 1 ^ 2 * b 5 + 3 * b 1 * b 3 ^ 2 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, powCoeff_zero_of_lt]
  ring

theorem p4_8 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 4 8 = 4 * b 1 ^ 3 * b 5 + 6 * b 1 ^ 2 * b 3 ^ 2 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, p3_7, p3_5,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p5_9 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 5 9 = 5 * b 1 ^ 4 * b 5 + 10 * b 1 ^ 3 * b 3 ^ 2 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, p4_8, p4_6,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p6_10 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 6 10 = 6 * b 1 ^ 5 * b 5 + 15 * b 1 ^ 4 * b 3 ^ 2 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, p5_9, p5_7,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p7_11 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 7 11 = 7 * b 1 ^ 6 * b 5 + 21 * b 1 ^ 5 * b 3 ^ 2 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, p6_10, p6_8,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p3_9 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    powCoeff b 3 9 = 3*b 1^2*b 7 + 6*b 1*b 3*b 5 + b 3^3 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6, b8]
  ring

theorem p4_10 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    powCoeff b 4 10 = 4*b 1^3*b 7 + 12*b 1^2*b 3*b 5 + 4*b 1*b 3^3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, p3_9, p3_7, p3_5,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p5_11 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    powCoeff b 5 11 = 5*b 1^4*b 7 + 20*b 1^3*b 3*b 5 +
      10*b 1^2*b 3^3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, p4_10, p4_8, p4_6,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

set_option maxHeartbeats 0 in
theorem p3_11 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0) :
    powCoeff b 3 11 = 3*b 1^2*b 9 + 6*b 1*b 3*b 7 +
      3*b 1*b 5^2 + 3*b 3^2*b 5 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6, b8, b10]
  ring

theorem composeCoeff_eleven_odd (a b : ℕ → ℂ)
    (a2 : a 2 = 0) (a4 : a 4 = 0) (a6 : a 6 = 0) (a8 : a 8 = 0)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0) :
    composeCoeff a b 11 = a 1*b 11 +
      a 3*(3*b 1^2*b 9 + 6*b 1*b 3*b 7 + 3*b 1*b 5^2 + 3*b 3^2*b 5) +
      a 5*(5*b 1^4*b 7 + 20*b 1^3*b 3*b 5 + 10*b 1^2*b 3^3) +
      a 7*(7*b 1^6*b 5 + 21*b 1^5*b 3^2) +
      a 9*(9*b 1^8*b 3) + a 11*b 1^11 := by
  simp only [composeCoeff, Finset.sum_range_succ]
  rw [a2, a4, a6, a8]
  simp only [zero_mul, add_zero]
  rw [powCoeff_one, p3_11 b b0 b2 b4 b6 b8 b10,
    p5_11 b b0 b2 b4 b6 b8, p7_11 b b0 b2 b4,
    p9_11 b b0 b2, powCoeff_next_diag_zero b b0 b2 10,
    powCoeff_diag b b0 11]
  simp [powCoeff, b0]

end GeneralCK.Certificates.E8ComposeCoeff11

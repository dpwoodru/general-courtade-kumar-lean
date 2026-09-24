import GeneralCK.PsiOuterEntropy2048

/-!
# Exact parent-polynomial logarithm comparisons

The shifted polynomial identities below expose every coefficient as a
positive rational.  They are intended as elementary inputs to the outer
active-psi parent comparison.
-/

namespace GeneralCK.PsiParentPolynomialBounds

noncomputable def P16 (x : ℝ) : ℝ :=
  1 + (837 / 128) * x + (3 / 16) * x ^ 2

noncomputable def P64 (x : ℝ) : ℝ :=
  1 + (1347 / 128) * x + (3 / 64) * x ^ 2

theorem log_P16_lt {x : ℝ} (hx : 16 ≤ x) :
    Real.log (P16 x) < 4 * Real.log (1 + 5 * x / 28) := by
  have hy : 0 ≤ x - 16 := by linarith
  have he : (1 + 5 * x / 28) ^ 4 - P16 x =
      625 * (x - 16) ^ 4 / 614656 +
      3375 * (x - 16) ^ 3 / 38416 +
      102147 * (x - 16) ^ 2 / 38416 +
      8743515 * (x - 16) / 307328 + 1300699 / 19208 := by
    unfold P16
    ring
  have hdiff : 0 < (1 + 5 * x / 28) ^ 4 - P16 x := by
    rw [he]
    positivity
  have hP : 0 < P16 x := by
    unfold P16
    positivity
  have hh := Real.log_lt_log hP
    (show P16 x < (1 + 5 * x / 28) ^ 4 by linarith)
  rw [Real.log_pow] at hh
  simpa using hh

theorem log_P64_lt_five_halves {x : ℝ} (hx : 40 ≤ x) :
    Real.log (P64 x) < (5 / 2) * Real.log (1 + 2 * x / 7) := by
  have hy : 0 ≤ x - 40 := by linarith
  have he : (1 + 2 * x / 7) ^ 5 - (P64 x) ^ 2 =
      32 * (x - 40) ^ 5 / 16807 +
      28356897 * (x - 40) ^ 4 / 68841472 +
      2388090753 * (x - 40) ^ 3 / 68841472 +
      362627237505 * (x - 40) ^ 2 / 275365888 +
      342500653701 * (x - 40) / 17210368 +
      213445891385 / 4302592 := by
    unfold P64
    ring
  have hdiff : 0 < (1 + 2 * x / 7) ^ 5 - (P64 x) ^ 2 := by
    rw [he]
    positivity
  have hP : 0 < P64 x := by
    unfold P64
    positivity
  have hh := Real.log_lt_log (pow_pos hP 2)
    (show (P64 x) ^ 2 < (1 + 2 * x / 7) ^ 5 by linarith)
  rw [Real.log_pow, Real.log_pow] at hh
  nlinarith

theorem log_seven_fifths_lt_two_fifths :
    Real.log (7 / 5 : ℝ) < 2 / 5 := by
  have hh := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 7 / 5) (by norm_num : (7 / 5 : ℝ) ≠ 1)
  norm_num at hh
  exact hh

theorem log_P64_lt_two_plus_two_fifths {x : ℝ} (hx : 75 ≤ x) :
    Real.log (P64 x) < 2 * Real.log (1 + 5 * x / 14) + 2 / 5 := by
  have hy : 0 ≤ x - 75 := by linarith
  have he : (7 / 5 : ℝ) * (1 + 5 * x / 14) ^ 2 - P64 x =
      59 * (x - 75) ^ 2 / 448 +
      9167 * (x - 75) / 896 + 120667 / 4480 := by
    unfold P64
    ring
  have hdiff : 0 < (7 / 5 : ℝ) * (1 + 5 * x / 14) ^ 2 - P64 x := by
    rw [he]
    positivity
  have hP : 0 < P64 x := by
    unfold P64
    positivity
  have hb : 0 < 1 + 5 * x / 14 := by positivity
  have hh := Real.log_lt_log hP
    (show P64 x < (7 / 5 : ℝ) * (1 + 5 * x / 14) ^ 2 by linarith)
  rw [Real.log_mul (by norm_num : (7 / 5 : ℝ) ≠ 0)
      (pow_ne_zero 2 hb.ne'), Real.log_pow] at hh
  linarith [log_seven_fifths_lt_two_fifths]

#print axioms log_P16_lt
#print axioms log_P64_lt_five_halves
#print axioms log_seven_fifths_lt_two_fifths
#print axioms log_P64_lt_two_plus_two_fifths

end GeneralCK.PsiParentPolynomialBounds

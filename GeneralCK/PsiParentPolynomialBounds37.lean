import GeneralCK.PsiParentPolynomialBounds

/-! A sharper exact polynomial threshold for the opposite-parent
medium-bias entropy-ratio exclusion. -/

namespace GeneralCK.PsiParentPolynomialBounds

theorem log_P64_lt_five_halves37 {x : ℝ} (hx : 37 ≤ x) :
    Real.log (P64 x) < (5 / 2) * Real.log (1 + 2 * x / 7) := by
  have hy : 0 ≤ x - 37 := by linarith
  have he : (1 + 2 * x / 7) ^ 5 - (P64 x) ^ 2 =
      32 * (x - 37) ^ 5 / 16807 +
      26390817 * (x - 37) ^ 4 / 68841472 +
      2059604469 * (x - 37) ^ 3 / 68841472 +
      282639502389 * (x - 37) ^ 2 / 275365888 +
      1775061496323 * (x - 37) / 137682944 +
      235297239857 / 275365888 := by
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

#print axioms log_P64_lt_five_halves37

end GeneralCK.PsiParentPolynomialBounds

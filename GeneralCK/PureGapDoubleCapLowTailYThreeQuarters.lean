import GeneralCK.PureGapDoubleCapLowTailDiagonalMarginPositive
import GeneralCK.PsiNormalizedLowEntropy

/-! An exact eighth-entropy anchor puts the low-tail inverse bias in the
three-quarter region where the diagonal margin has been certified. -/

namespace GeneralCK

theorem H_eighth_gt_half : (1 / 2 : ℝ) < H (1 / 8) := by
  have h := H_mul_log_two_ge (p := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
  have hInv : ((1 / 8 : ℝ)⁻¹) = 2 ^ (3 : ℕ) := by norm_num
  rw [hInv, Real.log_pow] at h
  nlinarith only [h, log_two_upper, log_two_pos]

theorem doubleCapLowTailY_ge_three_quarters {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    3 / 4 ≤ doubleCapLowTailY m := by
  have hh : 0 ≤ H (2 * m) / 2 := by
    exact div_nonneg (H_nonneg (by linarith) (by linarith)) (by norm_num)
  have hhalf : H (2 * m) / 2 ≤ H (1 / 8) := by
    linarith [H_le_one (2 * m), H_eighth_gt_half]
  have hinv := entropyInverse_mono hh (H_le_one (1 / 8)) hhalf
  rw [entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2)] at hinv
  dsimp [doubleCapLowTailY]
  linarith only [hinv]

#print axioms H_eighth_gt_half
#print axioms doubleCapLowTailY_ge_three_quarters

end GeneralCK

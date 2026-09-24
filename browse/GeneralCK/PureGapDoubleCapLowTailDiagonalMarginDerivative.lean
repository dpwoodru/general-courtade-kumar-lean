import GeneralCK.PureGapDoubleCapLowTailDiagonalBias
import GeneralCK.SmallMeanAnalytic

/-! A simple exact derivative for the diagonal bias margin. It shows that
the margin increases while `biasB<3/2` and decreases afterward; endpoint
and displacement bounds are still needed for the true low-tail slope sign. -/

namespace GeneralCK

open Certificates.Reflection Reflection

noncomputable def doubleCapDiagonalMargin (y : ℝ) : ℝ :=
  (1 - y ^ 2) * SmallMean.A y * biasB y - y * biasE y

theorem doubleCapDiagonalMargin_hasDerivAt {y : ℝ}
    (hy : 0 < y) (hy1 : y < 1) :
    HasDerivAt doubleCapDiagonalMargin
      (y * SmallMean.A y * (3 - 2 * biasB y)) y := by
  have hgap : 0 < 1 - y ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < 1 - y)
      (by linarith : 0 < 1 + y)]
  have hdgap : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * y) y := by
    have h := (((hasDerivAt_id y).pow 2).const_sub 1)
    change HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-(2 * y ^ (2 - 1) * 1)) y at h
    convert h using 1 <;> norm_num
  have hA := SmallMean.hasDerivAt_A (by linarith [hy]) hy1
  have hB := hasDerivAt_biasB (by linarith [hy]) hy1
  have hE := hasDerivAt_biasE (by linarith [hy]) hy1
  have h := ((hdgap.mul hA).mul hB).sub ((hasDerivAt_id y).mul hE)
  have heq : doubleCapDiagonalMargin =
      (fun z : ℝ => 1 - z ^ 2) * SmallMean.A * biasB - id * biasE := by
    funext z
    simp only [doubleCapDiagonalMargin, Pi.mul_apply, Pi.sub_apply, id_eq]
  rw [heq]
  convert! h using 1
  dsimp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  have hident := biasB_eq_biasE_add (by linarith [hy]) hy1
  have hcancel : (1 - y ^ 2) * (1 / (1 - y ^ 2)) = 1 := by
    field_simp [hgap.ne']
  have hcancel2 : ((1 - y ^ 2) * SmallMean.A y) *
      (y / (1 - y ^ 2)) = y * SmallMean.A y := by
    field_simp [hgap.ne']
  rw [hcancel]
  rw [hcancel2]
  nlinarith only [hident]

#print axioms doubleCapDiagonalMargin_hasDerivAt

end GeneralCK

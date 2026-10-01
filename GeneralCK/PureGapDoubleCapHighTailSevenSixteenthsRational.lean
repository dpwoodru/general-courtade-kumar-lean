import GeneralCK.PureGapDoubleCapHighTailRational

/-! Exact rational checker for the proposed wider `x≤1/8` high tail.
This source is a draft until a named Lean audit passes. -/

namespace GeneralCK

theorem doubleCapHighTailSeven_negative_rational_bound {u t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 64)
    (ht0 : 0 ≤ t) (htu : t ≤ (91 / 45 : ℝ) * u) :
    -(68152448 / 24350759 : ℝ) * u ≤
      2 - 2 / ((1 - t) * (1 + t / 3)) := by
  have htlim : t ≤ 91 / 2880 := by nlinarith [htu, hu1]
  have htsq : t ^ 2 ≤ (91 / 2880 : ℝ) * t := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr htlim)]
  let D : ℝ := (1 - t) * (1 + t / 3)
  have hD : (24350759 / 24883200 : ℝ) ≤ D := by
    dsimp [D]
    nlinarith [htlim, htsq]
  have hDpos : 0 < D := (by norm_num : (0 : ℝ) < 24350759 / 24883200).trans_le hD
  have hnum : 0 ≤ 2 * t + t ^ 2 := by positivity
  have hnumLe : 2 * t + t ^ 2 ≤ (5851 / 2880 : ℝ) * t := by
    nlinarith [htsq]
  have hcross :
      (2 * t + t ^ 2) * (24350759 / 24883200 : ℝ) ≤
      ((5851 / 2880 : ℝ) * t) * D := by
    have h1 := mul_le_mul_of_nonneg_right hnumLe
      (by norm_num : (0 : ℝ) ≤ 24350759 / 24883200)
    have h2 := mul_le_mul_of_nonneg_left hD
      (show 0 ≤ (5851 / 2880 : ℝ) * t by positivity)
    nlinarith [h1, h2]
  have hquot : (2 * t + t ^ 2) / D ≤
      ((5851 / 2880 : ℝ) * t) / (24350759 / 24883200 : ℝ) := by
    apply (div_le_div_iff₀ hDpos
      (by norm_num : (0 : ℝ) < 24350759 / 24883200)).2
    exact hcross
  have hratio : (2 / 3 : ℝ) *
      (((5851 / 2880 : ℝ) * t) / (24350759 / 24883200 : ℝ)) ≤
      (68152448 / 24350759 : ℝ) * u := by
    nlinarith [htu]
  have htOne : 0 < 1 - t := by linarith [htlim]
  have htPlus : 0 < 1 + t / 3 := by linarith [ht0]
  have heq : 2 - 2 / D = -(2 / 3 : ℝ) *
      ((2 * t + t ^ 2) / D) := by
    dsimp [D]
    field_simp [htOne.ne', htPlus.ne', hDpos.ne']
    ring
  rw [show (1 - t) * (1 + t / 3) = D by rfl, heq]
  nlinarith [hquot, hratio]

theorem doubleCapHighTailSeven_positive_rational_bound {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 64) :
    (1280 / 451 : ℝ) * u ≤
      2 * u / ((1 - u) * (7 / 10 + u)) := by
  have hgap : 0 < 1 - u := by linarith
  have hB : 0 < (7 / 10 : ℝ) + u := by linarith
  have hden : 0 < (1 - u) * (7 / 10 + u) := mul_pos hgap hB
  have hdenHi : (1 - u) * (7 / 10 + u) ≤ 451 / 640 := by
    nlinarith [hu1, sq_nonneg u]
  apply (le_div_iff₀ hden).2
  have hm := mul_le_mul_of_nonneg_left hdenHi hu0
  nlinarith [hm]

theorem doubleCapHighTailSeven_margin_pos :
    0 < (1280 / 451 : ℝ) - (68152448 / 24350759 : ℝ) := by
  norm_num

#print axioms doubleCapHighTailSeven_negative_rational_bound
#print axioms doubleCapHighTailSeven_positive_rational_bound
#print axioms doubleCapHighTailSeven_margin_pos

end GeneralCK

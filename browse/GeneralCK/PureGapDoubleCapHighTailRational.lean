import GeneralCK.SmallMeanCapTailBounds

/-! Small rational inequality isolated from the high double-cap logarithm
and implicit-contact proofs. -/

namespace GeneralCK

theorem doubleCapHighTail_negative_rational_bound {u t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 1024)
    (ht0 : 0 ≤ t) (htu : t ≤ (512 / 255 : ℝ) * u) :
    -(10455040 / 3893697 : ℝ) * u ≤
      2 - 2 / ((1 - t) * (1 + t / 3)) := by
  have htlim : t ≤ 1 / 510 := by nlinarith [htu, hu1]
  have htsq : t ^ 2 ≤ t / 510 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr htlim)]
  let D : ℝ := (1 - t) * (1 + t / 3)
  have hD : (499 / 500 : ℝ) ≤ D := by
    dsimp [D]
    nlinarith [htlim, htsq]
  have hDpos : 0 < D := (by norm_num : (0 : ℝ) < 499 / 500).trans_le hD
  have hnum : 0 ≤ 2 * t + t ^ 2 := by positivity
  have hnumLe : 2 * t + t ^ 2 ≤ (1021 / 510 : ℝ) * t := by
    nlinarith [htsq]
  have hcross :
      (2 * t + t ^ 2) * (499 / 500 : ℝ) ≤
        ((1021 / 510 : ℝ) * t) * D := by
    have h1 := mul_le_mul_of_nonneg_right hnumLe
      (by norm_num : (0 : ℝ) ≤ 499 / 500)
    have h2 := mul_le_mul_of_nonneg_left hD
      (show 0 ≤ (1021 / 510 : ℝ) * t by positivity)
    nlinarith [h1, h2]
  have hquot : (2 * t + t ^ 2) / D ≤
      ((1021 / 510 : ℝ) * t) / (499 / 500 : ℝ) := by
    apply (div_le_div_iff₀ hDpos
      (by norm_num : (0 : ℝ) < 499 / 500)).2
    exact hcross
  have hratio : (2 / 3 : ℝ) *
      (((1021 / 510 : ℝ) * t) / (499 / 500 : ℝ)) ≤
      (10455040 / 3893697 : ℝ) * u := by
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

theorem doubleCapHighTail_rational_margin_pos :
    0 < (10240 / 3589 : ℝ) - (10455040 / 3893697 : ℝ) := by
  norm_num

#print axioms doubleCapHighTail_negative_rational_bound
#print axioms doubleCapHighTail_rational_margin_pos

end GeneralCK

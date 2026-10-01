import GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsIdentity
import GeneralCK.LowInformationMeans

/-! Sharper exact inverse-entropy square bound proposed for `x≤1/8`.
This source is a draft until its named Lean audit passes. -/

namespace GeneralCK

theorem doubleCapHighTailSevenY_sq_le {x : ℝ}
    (hx : 0 < x) (hx8 : x ≤ 1 / 8) :
    0 ≤ doubleCapHighTailY x ∧
    doubleCapHighTailY x ^ 2 ≤ (91 / 45 : ℝ) * x ^ 2 ∧
    doubleCapHighTailY x ^ 2 ≤ 91 / 2880 := by
  have hx1 : x < 1 / 2 := by linarith
  have hh := doubleCapHighTailFloor_pos hx hx1
  have hh1 := doubleCapHighTailFloor_le_one hx hx1
  have hy0 : 0 ≤ doubleCapHighTailY x := by
    unfold doubleCapHighTailY
    linarith [(entropyInverse_spec hh.le hh1).2.1]
  have hy1 : doubleCapHighTailY x < 1 := by
    unfold doubleCapHighTailY
    linarith [entropyInverse_pos hh hh1]
  have hY := SmallMean.Cn_ge_half_sq hy0 hy1.le
  have hX := LowInformation.Cn_upper_sharp
    (show 0 ≤ 2 * x by positivity) (show 2 * x < 1 by linarith)
  have hEq := doubleCapHighTailY_deficit hx hx1
  have hu : x ^ 2 ≤ 1 / 64 := by
    have hsq := (sq_le_sq₀ hx.le
      (by norm_num : (0 : ℝ) ≤ 1 / 8)).2 hx8
    norm_num at hsq
    exact hsq
  have hgap : 0 < 1 - 4 * x ^ 2 := by nlinarith [hu]
  have hgap2 : 0 < 1 - (2 * x) ^ 2 := by nlinarith [hgap]
  have hXhalf : SmallMean.Cn (2 * x) / 2 ≤
      x ^ 2 + (2 / 3 : ℝ) * x ^ 4 / (1 - 4 * x ^ 2) := by
    have hdiv := div_le_div_of_nonneg_right hX (by norm_num : (0 : ℝ) ≤ 2)
    have heq :
        ((2 * x) ^ 2 / 2 + (2 * x) ^ 4 /
          (12 * (1 - (2 * x) ^ 2))) / 2 =
        x ^ 2 + (2 / 3 : ℝ) * x ^ 4 / (1 - 4 * x ^ 2) := by
      field_simp [hgap.ne', hgap2.ne']
      ring
    exact hdiv.trans_eq heq
  have hYraw : doubleCapHighTailY x ^ 2 ≤
      2 * x ^ 2 + (4 / 3 : ℝ) * x ^ 4 / (1 - 4 * x ^ 2) := by
    have hchain : doubleCapHighTailY x ^ 2 / 2 ≤
        x ^ 2 + (2 / 3 : ℝ) * x ^ 4 / (1 - 4 * x ^ 2) := by
      calc
        _ ≤ SmallMean.Cn (doubleCapHighTailY x) := hY
        _ = SmallMean.Cn (2 * x) / 2 := hEq
        _ ≤ _ := hXhalf
    have heq : 2 * (x ^ 2 + (2 / 3 : ℝ) * x ^ 4 /
        (1 - 4 * x ^ 2)) =
        2 * x ^ 2 + (4 / 3 : ℝ) * x ^ 4 /
          (1 - 4 * x ^ 2) := by ring
    rw [← heq]
    linarith [hchain]
  have hfrac : (4 / 3 : ℝ) * x ^ 4 / (1 - 4 * x ^ 2) ≤
      x ^ 2 / 45 := by
    apply (div_le_iff₀ hgap).2
    have hm := mul_le_mul_of_nonneg_left hu (sq_nonneg x)
    nlinarith [hm]
  have hsq : doubleCapHighTailY x ^ 2 ≤
      (91 / 45 : ℝ) * x ^ 2 := by
    linarith [hYraw, hfrac]
  refine ⟨hy0, hsq, ?_⟩
  nlinarith [hsq, hu]

#print axioms doubleCapHighTailSevenY_sq_le

end GeneralCK

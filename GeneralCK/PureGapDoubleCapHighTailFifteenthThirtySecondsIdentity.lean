import GeneralCK.PureGapDoubleCapHighTailIdentity

/-! Wider exact inverse-entropy square enclosure on x≤1/16. Draft until Lean audit. -/

namespace GeneralCK

theorem doubleCapHighTailFifteenthY_sq_le {x : ℝ}
    (hx : 0 < x) (hx16 : x ≤ 1 / 16) :
    0 ≤ doubleCapHighTailY x ∧
    doubleCapHighTailY x ^ 2 ≤ (128 / 63 : ℝ) * x ^ 2 ∧
    doubleCapHighTailY x ^ 2 ≤ 1 / 126 := by
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
  have hX := SmallMean.Cn_le_half_sq_over_gap
    (show 0 ≤ 2 * x by positivity) (show 2 * x < 1 by linarith)
  have hEq := doubleCapHighTailY_deficit hx hx1
  have hu : x ^ 2 ≤ 1 / 256 := by
    have hsq := (sq_le_sq₀ hx.le
      (by norm_num : (0 : ℝ) ≤ 1 / 16)).2 hx16
    norm_num at hsq
    exact hsq
  have hgap : 0 < 1 - 4 * x ^ 2 := by nlinarith [hu]
  have hgap2 : 0 < 1 - (2 * x) ^ 2 := by nlinarith [hgap]
  have hYraw : doubleCapHighTailY x ^ 2 / 2 ≤
      x ^ 2 / (1 - 4 * x ^ 2) := by
    have hX2 : SmallMean.Cn (2 * x) / 2 ≤
        (2 * x) ^ 2 / (4 * (1 - (2 * x) ^ 2)) := by
      calc
        _ ≤ ((2 * x) ^ 2 / (2 * (1 - (2 * x) ^ 2))) / 2 :=
          div_le_div_of_nonneg_right hX (by norm_num : (0 : ℝ) ≤ 2)
        _ = (2 * x) ^ 2 / (4 * (1 - (2 * x) ^ 2)) := by
          field_simp [hgap2.ne']
          ring
    calc
      _ ≤ SmallMean.Cn (doubleCapHighTailY x) := hY
      _ = SmallMean.Cn (2 * x) / 2 := hEq
      _ ≤ (2 * x) ^ 2 / (4 * (1 - (2 * x) ^ 2)) := hX2
      _ = x ^ 2 / (1 - 4 * x ^ 2) := by
        field_simp [hgap.ne']
        ring
  have hgapLo : (63 / 64 : ℝ) ≤ 1 - 4 * x ^ 2 := by nlinarith [hu]
  have hraw : doubleCapHighTailY x ^ 2 ≤
      2 * x ^ 2 / (1 - 4 * x ^ 2) := by
    have heq : 2 * (x ^ 2 / (1 - 4 * x ^ 2)) =
        2 * x ^ 2 / (1 - 4 * x ^ 2) := by ring
    rw [← heq]
    linarith [hYraw]
  have hrat : 2 * x ^ 2 / (1 - 4 * x ^ 2) ≤
      (128 / 63 : ℝ) * x ^ 2 := by
    apply (div_le_iff₀ hgap).2
    have hm := mul_le_mul_of_nonneg_left hgapLo
      (show 0 ≤ (128 / 63 : ℝ) * x ^ 2 by positivity)
    nlinarith [hm]
  have hsq : doubleCapHighTailY x ^ 2 ≤
      (128 / 63 : ℝ) * x ^ 2 := hraw.trans hrat
  refine ⟨hy0, hsq, ?_⟩
  nlinarith [hsq, hu]

#print axioms doubleCapHighTailFifteenthY_sq_le

end GeneralCK

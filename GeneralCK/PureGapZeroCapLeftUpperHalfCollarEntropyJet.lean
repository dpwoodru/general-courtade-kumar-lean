import GeneralCK.PureGapZeroCapLeftUpperHalfCollarLogJets

/-! Actual entropy quartic remainder obtained by integrating the accepted
slope error through a derivative comparison; no logarithm series premise. -/

namespace GeneralCK

private theorem sixth_barrier {f f' : ℝ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hzero : f 0 = 0)
    (hd : ∀ t ∈ Set.Icc 0 q, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Set.Icc 0 q, |f' t| ≤ 25 * t ^ 5) :
    |f q| ≤ (25 / 6 : ℝ) * q ^ 6 := by
  have hB (t : ℝ) : HasDerivAt (fun x : ℝ => (25 / 6 : ℝ) * x ^ 6)
      (25 * t ^ 5) t := by
    convert! (hasDerivAt_pow 6 t).const_mul (25 / 6 : ℝ) using 1 <;> norm_num <;> ring
  have hc : ContinuousOn f (Set.Icc 0 q) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hBc : ContinuousOn (fun x : ℝ => (25 / 6 : ℝ) * x ^ 6) (Set.Icc 0 q) :=
    fun t _ => (hB t).continuousAt.continuousWithinAt
  have hupper := image_le_of_deriv_right_le_deriv_boundary hc
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (show f 0 ≤ (25 / 6 : ℝ) * (0 : ℝ) ^ 6 by simp [hzero]) hBc
    (fun t _ => (hB t).hasDerivWithinAt)
    (fun t ht => (abs_le.mp (hb t ⟨ht.1, ht.2.le⟩)).2)
    (show q ∈ Set.Icc 0 q from ⟨hq, le_rfl⟩)
  have hlower := image_le_of_deriv_right_le_deriv_boundary hc.neg
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).neg.hasDerivWithinAt)
    (show -f 0 ≤ (25 / 6 : ℝ) * (0 : ℝ) ^ 6 by simp [hzero]) hBc
    (fun t _ => (hB t).hasDerivWithinAt)
    (fun t ht => (neg_le_iff_add_nonneg).2
      (by linarith [(abs_le.mp (hb t ⟨ht.1, ht.2.le⟩)).1]))
    (show q ∈ Set.Icc 0 q from ⟨hq, le_rfl⟩)
  change -f q ≤ _ at hlower
  exact abs_le.mpr ⟨by linarith, hupper⟩

theorem leftUpper_entropy_half_bias_quartic_remainder {q : ℝ}
    (hq : 0 ≤ q) (hqmax : q ≤ 1 / 64) :
    |1 - H (1 / 2 - q) - (2 * q ^ 2 / Real.log 2 +
        4 * q ^ 4 / (3 * Real.log 2))| ≤ (25 / 6 : ℝ) * q ^ 6 := by
  let E : ℝ → ℝ := fun t => 1 - H (1 / 2 - t) -
    (2 * t ^ 2 / Real.log 2 + 4 * t ^ 4 / (3 * Real.log 2))
  change |E q| ≤ _
  apply sixth_barrier hq (f' := fun t => J (1 / 2 - t) -
    (4 * t / Real.log 2 + 16 * t ^ 3 / (3 * Real.log 2)))
  · norm_num [E, H_half]
  · intro t ht
    have hdH := (Comparison.hasDerivAt_H
      (show 0 < 1 / 2 - t by linarith [ht.2])
      (show 1 / 2 - t < 1 by linarith [ht.1])).comp t
        ((hasDerivAt_id t).const_sub (1 / 2 : ℝ))
    have hd2 := ((hasDerivAt_pow 2 t).const_mul 2).div_const (Real.log 2)
    have hd4 := ((hasDerivAt_pow 4 t).const_mul 4).div_const (3 * Real.log 2)
    convert! (hdH.const_sub 1).sub (hd2.add hd4) using 1 <;> simp [E] <;> ring
  · intro t ht
    exact leftUpper_J_half_bias_cubic_remainder ht.1 (ht.2.trans hqmax)

#print axioms leftUpper_entropy_half_bias_quartic_remainder

end GeneralCK

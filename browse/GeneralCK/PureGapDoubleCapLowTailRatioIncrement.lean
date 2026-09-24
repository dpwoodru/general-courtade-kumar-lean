import GeneralCK.PureGapDoubleCapLowTailCoupling

/-! A quantitative derivative comparison for the true low-cap contact and
inverse-entropy bias. This is an analytic precursor to the low-tail sign. -/

namespace GeneralCK.Reflection

open Set Certificates.Reflection

theorem biasB_strictMonoOn_positive : StrictMonoOn biasB (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo (0 : ℝ) 1)
    (f' := fun x => x / (1 - x ^ 2))
  · intro x hx
    exact (hasDerivAt_biasB (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    exact (hasDerivAt_biasB (by linarith [hx.1]) hx.2).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    have hden : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos (by linarith [hx.2] : 0 < 1 - x)
        (by linarith [hx.1] : 0 < 1 + x)]
    exact div_pos hx.1 hden

/-- On a positive regular-contact interval, the regular ratio grows at
least at the derivative value at its left endpoint. -/
theorem regularRatio_increment_lower {c y : ℝ}
    (hc : 0 < c) (hcy : c ≤ y) (hy : y < 1) :
    (y - c) * (biasB c / (biasE c) ^ 2) ≤
      regularRatio y - regularRatio c := by
  have hc1 : c < 1 := lt_of_le_of_lt hcy hy
  have hcont : ContinuousOn regularRatio (Icc c y) := by
    intro x hx
    exact (hasDerivAt_regularRatio (by linarith [hc, hx.1])
      (by linarith [hy, hx.2])).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ regularRatio (interior (Icc c y)) := by
    intro x hx
    have hxi : x ∈ Ioo c y := by simpa only [interior_Icc] using hx
    exact (hasDerivAt_regularRatio (by linarith [hc, hxi.1])
      (by linarith [hy, hxi.2])).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Icc c y),
      biasB c / (biasE c) ^ 2 ≤ deriv regularRatio x := by
    intro x hx
    have hxi : x ∈ Ioo c y := by simpa only [interior_Icc] using hx
    have hB : biasB c ≤ biasB x :=
      biasB_strictMonoOn_positive.monotoneOn
        ⟨hc, hc1⟩ ⟨by linarith [hc, hxi.1], by linarith [hy, hxi.2]⟩ hxi.1.le
    have hE : biasE x ≤ biasE c :=
      biasE_antitone ⟨hc.le, hc1.le⟩
        ⟨by linarith [hc, hxi.1], by linarith [hy, hxi.2]⟩ hxi.1.le
    have hcE : 0 < biasE c := biasE_pos_wide (by linarith [hc]) hc1
    have hxE : 0 < biasE x := biasE_pos_wide
      (by linarith [hc, hxi.1]) (by linarith [hy, hxi.2])
    have hcB : 0 ≤ biasB c := (biasB_pos_wide (by linarith [hc]) hc1).le
    have hsE : (biasE x) ^ 2 ≤ (biasE c) ^ 2 := by nlinarith [hE]
    have hprod : biasB c * (biasE x) ^ 2 ≤
        biasB x * (biasE c) ^ 2 :=
      (mul_le_mul_of_nonneg_left hsE hcB).trans
        (mul_le_mul_of_nonneg_right hB (sq_nonneg _))
    rw [(hasDerivAt_regularRatio (by linarith [hc, hxi.1])
      (by linarith [hy, hxi.2])).deriv]
    exact (div_le_div_iff₀ (sq_pos_of_pos hcE) (sq_pos_of_pos hxE)).mpr hprod
  have hinc := (convex_Icc c y).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hderiv c ⟨le_rfl, hcy⟩ y ⟨hcy, le_rfl⟩ hcy
  simpa only [mul_comm] using hinc

#print axioms biasB_strictMonoOn_positive
#print axioms regularRatio_increment_lower

end GeneralCK.Reflection

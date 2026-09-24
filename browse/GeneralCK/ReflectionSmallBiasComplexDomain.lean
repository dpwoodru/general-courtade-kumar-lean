import GeneralCK.ReflectionComplexGlobalAnalytic

/-!
# A quantitative complex domain for the small-bias reflection argument

The closed bidisc of radius `21/50` maps strictly inside the existing
parameter disc of radius `7/10`. All constants below are rational.
-/

namespace GeneralCK.Reflection.SmallBiasComplexDomain

open ComplexEntropy ComplexGlobalAnalytic

private noncomputable def entropyPoly (c : ℂ) : ℂ :=
  c ^ 2 / 2 + c ^ 4 / 12 + c ^ 6 / 30

private lemma entropyPoly_identity (c : ℂ) :
    ((1 + c) * Complex.logTaylor 7 c +
      (1 - c) * Complex.logTaylor 7 (-c)) / 2 = entropyPoly c := by
  simp [Complex.logTaylor, Finset.sum_range_succ, entropyPoly]
  ring

private lemma norm_entropyPoly_le (c : ℂ) :
    ‖entropyPoly c‖ ≤ ‖c‖ ^ 2 / 2 + ‖c‖ ^ 4 / 12 + ‖c‖ ^ 6 / 30 := by
  unfold entropyPoly
  refine norm_add₃_le.trans_eq ?_
  simp only [norm_div, norm_pow]
  norm_num

private lemma norm_entropyRemainder_le {c : ℂ} (hc : ‖c‖ < 1) :
    ‖((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 7 c) +
      (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 7 (-c))) / 2‖ ≤
      (1 + ‖c‖) * (‖c‖ ^ 7 * (1 - ‖c‖)⁻¹ / 7) := by
  have hp := Complex.norm_log_sub_logTaylor_le 6 hc
  have hm := Complex.norm_log_sub_logTaylor_le 6 (z := -c) (by simpa using hc)
  norm_num at hp hm
  rw [norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  calc
    _ ≤ (‖(1 + c) * (Complex.log (1 + c) - Complex.logTaylor 7 c)‖ +
          ‖(1 - c) * (Complex.log (1 - c) - Complex.logTaylor 7 (-c))‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((1 + ‖c‖) * (‖c‖ ^ 7 * (1 - ‖c‖)⁻¹ / 7) +
          (1 + ‖c‖) * (‖c‖ ^ 7 * (1 - ‖c‖)⁻¹ / 7)) / 2 := by
      gcongr
      · rw [norm_mul]
        have hone : ‖(1 + c : ℂ)‖ ≤ 1 + ‖c‖ := by
          simpa using norm_add_le (1 : ℂ) c
        exact mul_le_mul hone hp (norm_nonneg _) (by positivity)
      · rw [norm_mul]
        have hone : ‖(1 - c : ℂ)‖ ≤ 1 + ‖c‖ := by
          simpa using norm_sub_le (1 : ℂ) c
        refine mul_le_mul hone ?_ (norm_nonneg _) (by positivity)
        simpa only [sub_eq_add_neg] using hm
    _ = _ := by ring

/-- The complex entropy loses at most `0.092` from `log 2` on the source disc. -/
theorem norm_entropyExt_sub_log_two_le {c : ℂ}
    (hc : ‖c‖ ≤ (21 / 50 : ℝ)) :
    ‖entropyExt c - (Real.log 2 : ℂ)‖ ≤ (92 / 1000 : ℝ) := by
  have hc1 : ‖c‖ < 1 := hc.trans_lt (by norm_num)
  have hinv : (1 - ‖c‖)⁻¹ ≤ (50 / 29 : ℝ) := by
    rw [inv_le_comm₀ (sub_pos.mpr hc1) (by norm_num : (0 : ℝ) < 50 / 29)]
    linarith
  have hid : entropyExt c - (Real.log 2 : ℂ) =
      -(entropyPoly c +
        ((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 7 c) +
          (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 7 (-c))) / 2) := by
    rw [← entropyPoly_identity c, entropyExt]
    ring
  rw [hid, norm_neg]
  calc
    _ ≤ ‖entropyPoly c‖ +
        ‖((1 + c) * (Complex.log (1 + c) - Complex.logTaylor 7 c) +
          (1 - c) * (Complex.log (1 - c) - Complex.logTaylor 7 (-c))) / 2‖ :=
      norm_add_le _ _
    _ ≤ (‖c‖ ^ 2 / 2 + ‖c‖ ^ 4 / 12 + ‖c‖ ^ 6 / 30) +
        (1 + ‖c‖) * (‖c‖ ^ 7 * (1 - ‖c‖)⁻¹ / 7) :=
      add_le_add (norm_entropyPoly_le c) (norm_entropyRemainder_le hc1)
    _ ≤ ((21 / 50 : ℝ) ^ 2 / 2 + (21 / 50 : ℝ) ^ 4 / 12 +
        (21 / 50 : ℝ) ^ 6 / 30) +
        (1 + (21 / 50 : ℝ)) * ((21 / 50 : ℝ) ^ 7 * (50 / 29 : ℝ) / 7) := by
      gcongr
    _ ≤ (92 / 1000 : ℝ) := by norm_num

noncomputable def meanEntropy (a b : ℂ) : ℂ := (entropyExt a + entropyExt b) / 2

theorem norm_meanEntropy_sub_log_two_le {a b : ℂ}
    (ha : ‖a‖ ≤ (21 / 50 : ℝ)) (hb : ‖b‖ ≤ (21 / 50 : ℝ)) :
    ‖meanEntropy a b - (Real.log 2 : ℂ)‖ ≤ (92 / 1000 : ℝ) := by
  have hid : meanEntropy a b - (Real.log 2 : ℂ) =
      ((entropyExt a - (Real.log 2 : ℂ)) +
        (entropyExt b - (Real.log 2 : ℂ))) / 2 := by
    unfold meanEntropy
    ring
  rw [hid, norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  have hh := norm_add_le (entropyExt a - (Real.log 2 : ℂ))
    (entropyExt b - (Real.log 2 : ℂ))
  have ha' := norm_entropyExt_sub_log_two_le ha
  have hb' := norm_entropyExt_sub_log_two_le hb
  linarith

theorem norm_meanEntropy_gt {a b : ℂ}
    (ha : ‖a‖ ≤ (21 / 50 : ℝ)) (hb : ‖b‖ ≤ (21 / 50 : ℝ)) :
    (601 / 1000 : ℝ) < ‖meanEntropy a b‖ := by
  have hnorm := norm_sub_norm_le (Real.log 2 : ℂ) (meanEntropy a b)
  rw [norm_sub_rev] at hnorm
  have hlog : ‖(Real.log 2 : ℂ)‖ = Real.log 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  rw [hlog] at hnorm
  have hh := norm_meanEntropy_sub_log_two_le ha hb
  have hlo := Real.log_two_gt_d9
  linarith

theorem meanEntropy_ne_zero {a b : ℂ}
    (ha : ‖a‖ ≤ (21 / 50 : ℝ)) (hb : ‖b‖ ≤ (21 / 50 : ℝ)) :
    meanEntropy a b ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_trans (by norm_num) (norm_meanEntropy_gt ha hb)

/-- Both signed reflection radii give parameters strictly inside the existing analytic disc. -/
theorem norm_parameter_lt {a b s : ℂ}
    (ha : ‖a‖ ≤ (21 / 50 : ℝ)) (hb : ‖b‖ ≤ (21 / 50 : ℝ))
    (hs : ‖s‖ ≤ (21 / 50 : ℝ)) :
    ‖s / meanEntropy a b‖ < (7 / 10 : ℝ) := by
  rw [norm_div]
  have he := norm_meanEntropy_gt ha hb
  apply (div_lt_iff₀ (lt_trans (by norm_num) he)).mpr
  linarith

end GeneralCK.Reflection.SmallBiasComplexDomain

import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell213
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (318737781 / 1000000000) ≤ -Real.log (2560 / 3521) ∧
    -Real.log (2560 / 3521) ≤ (159368891 / 500000000) := by
  have h := checkLog_sound (w := (961 / 6081)) (n := 12)
    (lo := (318737781 / 1000000000)) (hi := (159368891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3521 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3521 / 2560) = 1/(2560 / 3521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (318737781 / 1000000000) (159368891 / 500000000) (Real.log (3521 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3521 / 2560) = -Real.log (2560 / 3521) := by
    rw [show ((3521 / 2560) : ℝ) = ((2560 / 3521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (58828603 / 125000000) ≤ -Real.log (1599 / 2560) ∧
    -Real.log (1599 / 2560) ≤ (18825153 / 40000000) := by
  have h := checkLog_sound (w := (961 / 4159)) (n := 12)
    (lo := (58828603 / 125000000)) (hi := (18825153 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1599) = 1/(1599 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18825153 / 40000000) (-58828603 / 125000000) (Real.log (1599 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12732467 / 40000000) ≤ -Real.log (5120 / 7039) ∧
    -Real.log (5120 / 7039) ≤ (79577919 / 250000000) := by
  have h := checkLog_sound (w := (1919 / 12159)) (n := 12)
    (lo := (12732467 / 40000000)) (hi := (79577919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7039 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7039 / 5120) = 1/(5120 / 7039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12732467 / 40000000) (79577919 / 250000000) (Real.log (7039 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7039 / 5120) = -Real.log (5120 / 7039) := by
    rw [show ((7039 / 5120) : ℝ) = ((5120 / 7039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (234845589 / 500000000) ≤ -Real.log (3201 / 5120) ∧
    -Real.log (3201 / 5120) ≤ (469691179 / 1000000000) := by
  have h := checkLog_sound (w := (1919 / 8321)) (n := 12)
    (lo := (234845589 / 500000000)) (hi := (469691179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3201) = 1/(3201 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-469691179 / 1000000000) (-234845589 / 500000000) (Real.log (3201 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (59098839 / 250000000) ≤ -Real.log (40000 / 50667) ∧
    -Real.log (40000 / 50667) ≤ (236395357 / 1000000000) := by
  have h := checkLog_sound (w := (10667 / 90667)) (n := 12)
    (lo := (59098839 / 250000000)) (hi := (236395357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50667 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50667 / 40000) = 1/(40000 / 50667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (59098839 / 250000000) (236395357 / 1000000000) (Real.log (50667 / 40000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (50667 / 40000) = -Real.log (40000 / 50667) := by
    rw [show ((50667 / 40000) : ℝ) = ((40000 / 50667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (77541573 / 250000000) ≤ -Real.log (29333 / 40000) ∧
    -Real.log (29333 / 40000) ≤ (310166293 / 1000000000) := by
  have h := checkLog_sound (w := (10667 / 69333)) (n := 12)
    (lo := (77541573 / 250000000)) (hi := (310166293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 29333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 29333) = 1/(29333 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-310166293 / 1000000000) (-77541573 / 250000000) (Real.log (29333 / 40000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (47346007 / 200000000) ≤ -Real.log (1000000 / 1267099) ∧
    -Real.log (1000000 / 1267099) ≤ (59182509 / 250000000) := by
  have h := checkLog_sound (w := (267099 / 2267099)) (n := 12)
    (lo := (47346007 / 200000000)) (hi := (59182509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267099 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267099 / 1000000) = 1/(1000000 / 1267099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (47346007 / 200000000) (59182509 / 250000000) (Real.log (1267099 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1267099 / 1000000) = -Real.log (1000000 / 1267099) := by
    rw [show ((1267099 / 1000000) : ℝ) = ((1000000 / 1267099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (310744647 / 1000000000) ≤ -Real.log (732901 / 1000000) ∧
    -Real.log (732901 / 1000000) ≤ (38843081 / 125000000) := by
  have h := checkLog_sound (w := (267099 / 1732901)) (n := 12)
    (lo := (310744647 / 1000000000)) (hi := (38843081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732901) = 1/(732901 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-38843081 / 125000000) (-310744647 / 1000000000) (Real.log (732901 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8796601 / 50000000) ≤ -Real.log (1000000 / 1192357) ∧
    -Real.log (1000000 / 1192357) ≤ (175932021 / 1000000000) := by
  have h := checkLog_sound (w := (192357 / 2192357)) (n := 12)
    (lo := (8796601 / 50000000)) (hi := (175932021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192357 / 1000000) = 1/(1000000 / 1192357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8796601 / 50000000) (175932021 / 1000000000) (Real.log (1192357 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1192357 / 1000000) = -Real.log (1000000 / 1192357) := by
    rw [show ((1192357 / 1000000) : ℝ) = ((1000000 / 1192357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (213635149 / 1000000000) ≤ -Real.log (807643 / 1000000) ∧
    -Real.log (807643 / 1000000) ≤ (4272703 / 20000000) := by
  have h := checkLog_sound (w := (192357 / 1807643)) (n := 12)
    (lo := (213635149 / 1000000000)) (hi := (4272703 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807643) = 1/(807643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4272703 / 20000000) (-213635149 / 1000000000) (Real.log (807643 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (176198683 / 1000000000) ≤ -Real.log (40000 / 47707) ∧
    -Real.log (40000 / 47707) ≤ (44049671 / 250000000) := by
  have h := checkLog_sound (w := (7707 / 87707)) (n := 12)
    (lo := (176198683 / 1000000000)) (hi := (44049671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47707 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47707 / 40000) = 1/(40000 / 47707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (176198683 / 1000000000) (44049671 / 250000000) (Real.log (47707 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (47707 / 40000) = -Real.log (40000 / 47707) := by
    rw [show ((47707 / 40000) : ℝ) = ((40000 / 47707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (42805793 / 200000000) ≤ -Real.log (32293 / 40000) ∧
    -Real.log (32293 / 40000) ≤ (107014483 / 500000000) := by
  have h := checkLog_sound (w := (7707 / 72293)) (n := 12)
    (lo := (42805793 / 200000000)) (hi := (107014483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32293) = 1/(32293 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-107014483 / 500000000) (-42805793 / 200000000) (Real.log (32293 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (788002853 / 1000000000) ≤ -Real.log (500000000000 / 1099500156201) ∧
    -Real.log (500000000000 / 1099500156201) ≤ (157600571 / 200000000) := by
  have h := checkLog_sound (w := (99500156201 / 2099500156201)) (n := 12)
    (lo := (94855673 / 1000000000)) (hi := (47427837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099500156201 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1099500156201 / 1000000000000) = 1/(500000000000 / 1099500156201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (788002853 / 1000000000) (157600571 / 200000000) (Real.log (1099500156201 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1099500156201 / 500000000000) = -Real.log (500000000000 / 1099500156201) := by
    rw [show ((1099500156201 / 500000000000) : ℝ) = ((500000000000 / 1099500156201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (157873321 / 200000000) ≤ -Real.log (500000000000 / 1101000625391) ∧
    -Real.log (500000000000 / 1101000625391) ≤ (789366607 / 1000000000) := by
  have h := checkLog_sound (w := (101000625391 / 2101000625391)) (n := 12)
    (lo := (3848777 / 40000000)) (hi := (48109713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101000625391 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1101000625391 / 1000000000000) = 1/(500000000000 / 1101000625391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (157873321 / 200000000) (789366607 / 1000000000) (Real.log (1101000625391 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1101000625391 / 500000000000) = -Real.log (500000000000 / 1101000625391) := by
    rw [show ((1101000625391 / 500000000000) : ℝ) = ((500000000000 / 1101000625391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (34160103 / 62500000) ≤ -Real.log (3125000000 / 5397824123) ∧
    -Real.log (3125000000 / 5397824123) ≤ (546561649 / 1000000000) := by
  have h := checkLog_sound (w := (2272824123 / 8522824123)) (n := 12)
    (lo := (34160103 / 62500000)) (hi := (546561649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5397824123 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5397824123 / 3125000000) = 1/(3125000000 / 5397824123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (34160103 / 62500000) (546561649 / 1000000000) (Real.log (5397824123 / 3125000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (5397824123 / 3125000000) = -Real.log (3125000000 / 5397824123) := by
    rw [show ((5397824123 / 3125000000) : ℝ) = ((3125000000 / 5397824123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (547474683 / 1000000000) ≤ -Real.log (500000000000 / 864440763487) ∧
    -Real.log (500000000000 / 864440763487) ≤ (136868671 / 250000000) := by
  have h := checkLog_sound (w := (364440763487 / 1364440763487)) (n := 12)
    (lo := (547474683 / 1000000000)) (hi := (136868671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((864440763487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(864440763487 / 500000000000) = 1/(500000000000 / 864440763487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (547474683 / 1000000000) (136868671 / 250000000) (Real.log (864440763487 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (864440763487 / 500000000000) = -Real.log (500000000000 / 864440763487) := by
    rw [show ((864440763487 / 500000000000) : ℝ) = ((500000000000 / 864440763487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (38956717 / 100000000) ≤ -Real.log (125000000000 / 184542706369) ∧
    -Real.log (125000000000 / 184542706369) ≤ (389567171 / 1000000000) := by
  have h := checkLog_sound (w := (59542706369 / 309542706369)) (n := 12)
    (lo := (38956717 / 100000000)) (hi := (389567171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184542706369 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184542706369 / 125000000000) = 1/(125000000000 / 184542706369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (38956717 / 100000000) (389567171 / 1000000000) (Real.log (184542706369 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (184542706369 / 125000000000) = -Real.log (125000000000 / 184542706369) := by
    rw [show ((184542706369 / 125000000000) : ℝ) = ((125000000000 / 184542706369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (390227649 / 1000000000) ≤ -Real.log (500000000000 / 738658532809) ∧
    -Real.log (500000000000 / 738658532809) ≤ (7804553 / 20000000) := by
  have h := checkLog_sound (w := (238658532809 / 1238658532809)) (n := 12)
    (lo := (390227649 / 1000000000)) (hi := (7804553 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738658532809 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738658532809 / 500000000000) = 1/(500000000000 / 738658532809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (390227649 / 1000000000) (7804553 / 20000000) (Real.log (738658532809 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (738658532809 / 500000000000) = -Real.log (500000000000 / 738658532809) := by
    rw [show ((738658532809 / 500000000000) : ℝ) = ((500000000000 / 738658532809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (18915141 / 500000000) ≤ -Real.log (1540602151 / 1600000000) ∧
    -Real.log (1540602151 / 1600000000) ≤ (37830283 / 1000000000) := by
  have h := checkLog_sound (w := (59397849 / 3140602151)) (n := 12)
    (lo := (18915141 / 500000000)) (hi := (37830283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1540602151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1540602151) = 1/(1540602151 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37830283 / 1000000000) (-18915141 / 500000000) (Real.log (1540602151 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37703129 / 1000000000) ≤ -Real.log (962998784551 / 1000000000000) ∧
    -Real.log (962998784551 / 1000000000000) ≤ (3770313 / 100000000) := by
  have h := checkLog_sound (w := (37001215449 / 1962998784551)) (n := 12)
    (lo := (37703129 / 1000000000)) (hi := (3770313 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962998784551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962998784551) = 1/(962998784551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3770313 / 100000000) (-37703129 / 1000000000) (Real.log (962998784551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell213

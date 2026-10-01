import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell152
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

theorem reflection_log_1_neg : (292407219 / 1000000000) ≤ -Real.log (5120 / 6859) ∧
    -Real.log (5120 / 6859) ≤ (14620361 / 50000000) := by
  have h := checkLog_sound (w := (1739 / 11979)) (n := 12)
    (lo := (292407219 / 1000000000)) (hi := (14620361 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6859 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6859 / 5120) = 1/(5120 / 6859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (292407219 / 1000000000) (14620361 / 50000000) (Real.log (6859 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6859 / 5120) = -Real.log (5120 / 6859) := by
    rw [show ((6859 / 5120) : ℝ) = ((5120 / 6859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (82996583 / 200000000) ≤ -Real.log (3381 / 5120) ∧
    -Real.log (3381 / 5120) ≤ (103745729 / 250000000) := by
  have h := checkLog_sound (w := (1739 / 8501)) (n := 12)
    (lo := (82996583 / 200000000)) (hi := (103745729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3381) = 1/(3381 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-103745729 / 250000000) (-82996583 / 200000000) (Real.log (3381 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (145984871 / 500000000) ≤ -Real.log (640 / 857) ∧
    -Real.log (640 / 857) ≤ (291969743 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1497)) (n := 12)
    (lo := (145984871 / 500000000)) (hi := (291969743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(857 / 640) = 1/(640 / 857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (145984871 / 500000000) (291969743 / 1000000000) (Real.log (857 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (857 / 640) = -Real.log (640 / 857) := by
    rw [show ((857 / 640) : ℝ) = ((640 / 857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (414095997 / 1000000000) ≤ -Real.log (423 / 640) ∧
    -Real.log (423 / 640) ≤ (207047999 / 500000000) := by
  have h := checkLog_sound (w := (217 / 1063)) (n := 12)
    (lo := (414095997 / 1000000000)) (hi := (207047999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 423) = 1/(423 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-207047999 / 500000000) (-414095997 / 1000000000) (Real.log (423 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (215885273 / 1000000000) ≤ -Real.log (3125 / 3878) ∧
    -Real.log (3125 / 3878) ≤ (107942637 / 500000000) := by
  have h := checkLog_sound (w := (753 / 7003)) (n := 12)
    (lo := (215885273 / 1000000000)) (hi := (107942637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3878 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3878 / 3125) = 1/(3125 / 3878) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (215885273 / 1000000000) (107942637 / 500000000) (Real.log (3878 / 3125)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3878 / 3125) = -Real.log (3125 / 3878) := by
    rw [show ((3878 / 3125) : ℝ) = ((3125 / 3878) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (137850401 / 500000000) ≤ -Real.log (2372 / 3125) ∧
    -Real.log (2372 / 3125) ≤ (275700803 / 1000000000) := by
  have h := checkLog_sound (w := (753 / 5497)) (n := 12)
    (lo := (137850401 / 500000000)) (hi := (275700803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2372) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2372) = 1/(2372 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-275700803 / 1000000000) (-137850401 / 500000000) (Real.log (2372 / 3125)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (216224469 / 1000000000) ≤ -Real.log (1000000 / 1241381) ∧
    -Real.log (1000000 / 1241381) ≤ (21622447 / 100000000) := by
  have h := checkLog_sound (w := (241381 / 2241381)) (n := 12)
    (lo := (216224469 / 1000000000)) (hi := (21622447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241381 / 1000000) = 1/(1000000 / 1241381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (216224469 / 1000000000) (21622447 / 100000000) (Real.log (1241381 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1241381 / 1000000) = -Real.log (1000000 / 1241381) := by
    rw [show ((1241381 / 1000000) : ℝ) = ((1000000 / 1241381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (276255603 / 1000000000) ≤ -Real.log (758619 / 1000000) ∧
    -Real.log (758619 / 1000000) ≤ (69063901 / 250000000) := by
  have h := checkLog_sound (w := (241381 / 1758619)) (n := 12)
    (lo := (276255603 / 1000000000)) (hi := (69063901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758619) = 1/(758619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-69063901 / 250000000) (-276255603 / 1000000000) (Real.log (758619 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79854743 / 500000000) ≤ -Real.log (100000 / 117317) ∧
    -Real.log (100000 / 117317) ≤ (159709487 / 1000000000) := by
  have h := checkLog_sound (w := (17317 / 217317)) (n := 12)
    (lo := (79854743 / 500000000)) (hi := (159709487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117317 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117317 / 100000) = 1/(100000 / 117317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79854743 / 500000000) (159709487 / 1000000000) (Real.log (117317 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (117317 / 100000) = -Real.log (100000 / 117317) := by
    rw [show ((117317 / 100000) : ℝ) = ((100000 / 117317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (190156167 / 1000000000) ≤ -Real.log (82683 / 100000) ∧
    -Real.log (82683 / 100000) ≤ (23769521 / 125000000) := by
  have h := checkLog_sound (w := (17317 / 182683)) (n := 12)
    (lo := (190156167 / 1000000000)) (hi := (23769521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82683) = 1/(82683 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-23769521 / 125000000) (-190156167 / 1000000000) (Real.log (82683 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (159976249 / 1000000000) ≤ -Real.log (1000000 / 1173483) ∧
    -Real.log (1000000 / 1173483) ≤ (127981 / 800000) := by
  have h := checkLog_sound (w := (173483 / 2173483)) (n := 12)
    (lo := (159976249 / 1000000000)) (hi := (127981 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1173483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1173483 / 1000000) = 1/(1000000 / 1173483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (159976249 / 1000000000) (127981 / 800000) (Real.log (1173483 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1173483 / 1000000) = -Real.log (1000000 / 1173483) := by
    rw [show ((1173483 / 1000000) : ℝ) = ((1000000 / 1173483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (190534793 / 1000000000) ≤ -Real.log (826517 / 1000000) ∧
    -Real.log (826517 / 1000000) ≤ (95267397 / 500000000) := by
  have h := checkLog_sound (w := (173483 / 1826517)) (n := 12)
    (lo := (190534793 / 1000000000)) (hi := (95267397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 826517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 826517) = 1/(826517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-95267397 / 500000000) (-190534793 / 1000000000) (Real.log (826517 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (353032869 / 500000000) ≤ -Real.log (250000000000 / 506501182033) ∧
    -Real.log (250000000000 / 506501182033) ≤ (35303287 / 50000000) := by
  have h := checkLog_sound (w := (6501182033 / 1006501182033)) (n := 12)
    (lo := (6459279 / 500000000)) (hi := (12918559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((506501182033 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(506501182033 / 500000000000) = 1/(250000000000 / 506501182033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (353032869 / 500000000) (35303287 / 50000000) (Real.log (506501182033 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (506501182033 / 250000000000) = -Real.log (250000000000 / 506501182033) := by
    rw [show ((506501182033 / 250000000000) : ℝ) = ((250000000000 / 506501182033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (353695067 / 500000000) ≤ -Real.log (500000000000 / 1014344868383) ∧
    -Real.log (500000000000 / 1014344868383) ≤ (88423767 / 125000000) := by
  have h := checkLog_sound (w := (14344868383 / 2014344868383)) (n := 12)
    (lo := (7121477 / 500000000)) (hi := (2848591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1014344868383 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1014344868383 / 1000000000000) = 1/(500000000000 / 1014344868383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (353695067 / 500000000) (88423767 / 125000000) (Real.log (1014344868383 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1014344868383 / 500000000000) = -Real.log (500000000000 / 1014344868383) := by
    rw [show ((1014344868383 / 500000000000) : ℝ) = ((500000000000 / 1014344868383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (19663443 / 40000000) ≤ -Real.log (15625000000 / 25545425801) ∧
    -Real.log (15625000000 / 25545425801) ≤ (122896519 / 250000000) := by
  have h := checkLog_sound (w := (9920425801 / 41170425801)) (n := 12)
    (lo := (19663443 / 40000000)) (hi := (122896519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25545425801 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25545425801 / 15625000000) = 1/(15625000000 / 25545425801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19663443 / 40000000) (122896519 / 250000000) (Real.log (25545425801 / 15625000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (25545425801 / 15625000000) = -Real.log (15625000000 / 25545425801) := by
    rw [show ((25545425801 / 15625000000) : ℝ) = ((15625000000 / 25545425801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (492480073 / 1000000000) ≤ -Real.log (500000000000 / 818184754139) ∧
    -Real.log (500000000000 / 818184754139) ≤ (246240037 / 500000000) := by
  have h := checkLog_sound (w := (318184754139 / 1318184754139)) (n := 12)
    (lo := (492480073 / 1000000000)) (hi := (246240037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818184754139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818184754139 / 500000000000) = 1/(500000000000 / 818184754139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (492480073 / 1000000000) (246240037 / 500000000) (Real.log (818184754139 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (818184754139 / 500000000000) = -Real.log (500000000000 / 818184754139) := by
    rw [show ((818184754139 / 500000000000) : ℝ) = ((500000000000 / 818184754139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (174932827 / 500000000) ≤ -Real.log (125000000000 / 177359614431) ∧
    -Real.log (125000000000 / 177359614431) ≤ (69973131 / 200000000) := by
  have h := checkLog_sound (w := (52359614431 / 302359614431)) (n := 12)
    (lo := (174932827 / 500000000)) (hi := (69973131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177359614431 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177359614431 / 125000000000) = 1/(125000000000 / 177359614431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (174932827 / 500000000) (69973131 / 200000000) (Real.log (177359614431 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (177359614431 / 125000000000) = -Real.log (125000000000 / 177359614431) := by
    rw [show ((177359614431 / 125000000000) : ℝ) = ((125000000000 / 177359614431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (175255521 / 500000000) ≤ -Real.log (12500000000 / 17747411729) ∧
    -Real.log (12500000000 / 17747411729) ≤ (350511043 / 1000000000) := by
  have h := checkLog_sound (w := (5247411729 / 30247411729)) (n := 12)
    (lo := (175255521 / 500000000)) (hi := (350511043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17747411729 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17747411729 / 12500000000) = 1/(12500000000 / 17747411729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (175255521 / 500000000) (350511043 / 1000000000) (Real.log (17747411729 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (17747411729 / 12500000000) = -Real.log (12500000000 / 17747411729) := by
    rw [show ((17747411729 / 12500000000) : ℝ) = ((12500000000 / 17747411729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (30558543 / 1000000000) ≤ -Real.log (969903648711 / 1000000000000) ∧
    -Real.log (969903648711 / 1000000000000) ≤ (1909909 / 62500000) := by
  have h := checkLog_sound (w := (30096351289 / 1969903648711)) (n := 12)
    (lo := (30558543 / 1000000000)) (hi := (1909909 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969903648711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969903648711) = 1/(969903648711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1909909 / 62500000) (-30558543 / 1000000000) (Real.log (969903648711 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (761167 / 25000000) ≤ -Real.log (9700121511 / 10000000000) ∧
    -Real.log (9700121511 / 10000000000) ≤ (30446681 / 1000000000) := by
  have h := checkLog_sound (w := (299878489 / 19700121511)) (n := 12)
    (lo := (761167 / 25000000)) (hi := (30446681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9700121511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9700121511) = 1/(9700121511 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-30446681 / 1000000000) (-761167 / 25000000) (Real.log (9700121511 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell152

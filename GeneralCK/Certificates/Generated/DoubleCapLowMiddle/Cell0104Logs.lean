import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0104
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (67064991 / 100000000) ≤ -Real.log (25600 / 50061) ∧
    -Real.log (25600 / 50061) ≤ (670649911 / 1000000000) := by
  have h := checkLog_sound (w := (24461 / 75661)) (n := 12)
    (lo := (67064991 / 100000000)) (hi := (670649911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50061 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50061 / 25600) = 1/(25600 / 50061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67064991 / 100000000) (670649911 / 1000000000) (Real.log (50061 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50061 / 25600) = -Real.log (25600 / 50061) := by
    rw [show ((50061 / 25600) : ℝ) = ((25600 / 50061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (48631901 / 15625000) ≤ -Real.log (1139 / 25600) ∧
    -Real.log (1139 / 25600) ≤ (3112441669 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 2739)) (n := 12)
    (lo := (21240809 / 62500000)) (hi := (67970589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1139) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1139) = 1/(1139 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3112441669 / 1000000000) (-48631901 / 15625000) (Real.log (1139 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (670460123 / 1000000000) ≤ -Real.log (51200 / 100103) ∧
    -Real.log (51200 / 100103) ≤ (167615031 / 250000000) := by
  have h := checkLog_sound (w := (48903 / 151303)) (n := 12)
    (lo := (670460123 / 1000000000)) (hi := (167615031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100103 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100103 / 51200) = 1/(51200 / 100103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (670460123 / 1000000000) (167615031 / 250000000) (Real.log (100103 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100103 / 51200) = -Real.log (51200 / 100103) := by
    rw [show ((100103 / 51200) : ℝ) = ((51200 / 100103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1552067803 / 500000000) ≤ -Real.log (2297 / 51200) ∧
    -Real.log (2297 / 51200) ≤ (3104135611 / 1000000000) := by
  have h := checkLog_sound (w := (903 / 5497)) (n := 12)
    (lo := (165773443 / 500000000)) (hi := (331546887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2297) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2297) = 1/(2297 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3104135611 / 1000000000) (-1552067803 / 500000000) (Real.log (2297 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (647634841 / 1000000000) ≤ -Real.log (12800 / 24461) ∧
    -Real.log (12800 / 24461) ≤ (323817421 / 500000000) := by
  have h := checkLog_sound (w := (11661 / 37261)) (n := 12)
    (lo := (647634841 / 1000000000)) (hi := (323817421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24461 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24461 / 12800) = 1/(12800 / 24461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (647634841 / 1000000000) (323817421 / 500000000) (Real.log (24461 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24461 / 12800) = -Real.log (12800 / 24461) := by
    rw [show ((24461 / 12800) : ℝ) = ((12800 / 24461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (604823621 / 250000000) ≤ -Real.log (1139 / 12800) ∧
    -Real.log (1139 / 12800) ≤ (302411811 / 125000000) := by
  have h := checkLog_sound (w := (461 / 2739)) (n := 12)
    (lo := (21240809 / 62500000)) (hi := (67970589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1139) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1139) = 1/(1139 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-302411811 / 125000000) (-604823621 / 250000000) (Real.log (1139 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (80905799 / 125000000) ≤ -Real.log (25600 / 48903) ∧
    -Real.log (25600 / 48903) ≤ (647246393 / 1000000000) := by
  have h := checkLog_sound (w := (23303 / 74503)) (n := 12)
    (lo := (80905799 / 125000000)) (hi := (647246393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48903 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48903 / 25600) = 1/(25600 / 48903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (80905799 / 125000000) (647246393 / 1000000000) (Real.log (48903 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48903 / 25600) = -Real.log (25600 / 48903) := by
    rw [show ((48903 / 25600) : ℝ) = ((25600 / 48903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1205494213 / 500000000) ≤ -Real.log (2297 / 25600) ∧
    -Real.log (2297 / 25600) ≤ (241098843 / 100000000) := by
  have h := checkLog_sound (w := (903 / 5497)) (n := 12)
    (lo := (165773443 / 500000000)) (hi := (331546887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2297) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2297) = 1/(2297 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-241098843 / 100000000) (-1205494213 / 500000000) (Real.log (2297 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (337312601 / 500000000) ≤ -Real.log (1000000 / 1963297) ∧
    -Real.log (1000000 / 1963297) ≤ (674625203 / 1000000000) := by
  have h := checkLog_sound (w := (963297 / 2963297)) (n := 12)
    (lo := (337312601 / 500000000)) (hi := (674625203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963297 / 1000000) = 1/(1000000 / 1963297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (337312601 / 500000000) (674625203 / 1000000000) (Real.log (1963297 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1963297 / 1000000) = -Real.log (1000000 / 1963297) := by
    rw [show ((1963297 / 1000000) : ℝ) = ((1000000 / 1963297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3304896781 / 1000000000) ≤ -Real.log (36703 / 1000000) ∧
    -Real.log (36703 / 1000000) ≤ (1652448393 / 500000000) := by
  have h := checkLog_sound (w := (25797 / 99203)) (n := 12)
    (lo := (532308061 / 1000000000)) (hi := (266154031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36703) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36703) = 1/(36703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1652448393 / 500000000) (-3304896781 / 1000000000) (Real.log (36703 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (134954173 / 200000000) ≤ -Real.log (1000000 / 1963583) ∧
    -Real.log (1000000 / 1963583) ≤ (337385433 / 500000000) := by
  have h := checkLog_sound (w := (963583 / 2963583)) (n := 12)
    (lo := (134954173 / 200000000)) (hi := (337385433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963583 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963583 / 1000000) = 1/(1000000 / 1963583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (134954173 / 200000000) (337385433 / 500000000) (Real.log (1963583 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1963583 / 1000000) = -Real.log (1000000 / 1963583) := by
    rw [show ((1963583 / 1000000) : ℝ) = ((1000000 / 1963583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1656359789 / 500000000) ≤ -Real.log (36417 / 1000000) ∧
    -Real.log (36417 / 1000000) ≤ (3312719583 / 1000000000) := by
  have h := checkLog_sound (w := (26083 / 98917)) (n := 12)
    (lo := (270065429 / 500000000)) (hi := (540130859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36417) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36417) = 1/(36417 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3312719583 / 1000000000) (-1656359789 / 500000000) (Real.log (36417 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (674433669 / 1000000000) ≤ -Real.log (1000000 / 1962921) ∧
    -Real.log (1000000 / 1962921) ≤ (67443367 / 100000000) := by
  have h := checkLog_sound (w := (962921 / 2962921)) (n := 12)
    (lo := (674433669 / 1000000000)) (hi := (67443367 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962921 / 1000000) = 1/(1000000 / 1962921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (674433669 / 1000000000) (67443367 / 100000000) (Real.log (1962921 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1962921 / 1000000) = -Real.log (1000000 / 1962921) := by
    rw [show ((1962921 / 1000000) : ℝ) = ((1000000 / 1962921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (658940901 / 200000000) ≤ -Real.log (37079 / 1000000) ∧
    -Real.log (37079 / 1000000) ≤ (329470451 / 100000000) := by
  have h := checkLog_sound (w := (25421 / 99579)) (n := 12)
    (lo := (104423157 / 200000000)) (hi := (261057893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37079) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37079) = 1/(37079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-329470451 / 100000000) (-658940901 / 200000000) (Real.log (37079 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (134916687 / 200000000) ≤ -Real.log (200000 / 392643) ∧
    -Real.log (200000 / 392643) ≤ (168645859 / 250000000) := by
  have h := checkLog_sound (w := (192643 / 592643)) (n := 12)
    (lo := (134916687 / 200000000)) (hi := (168645859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392643 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392643 / 200000) = 1/(200000 / 392643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (134916687 / 200000000) (168645859 / 250000000) (Real.log (392643 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (392643 / 200000) = -Real.log (200000 / 392643) := by
    rw [show ((392643 / 200000) : ℝ) = ((200000 / 392643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3302665123 / 1000000000) ≤ -Real.log (7357 / 200000) ∧
    -Real.log (7357 / 200000) ≤ (412833141 / 125000000) := by
  have h := checkLog_sound (w := (5143 / 19857)) (n := 12)
    (lo := (530076403 / 1000000000)) (hi := (132519101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7357) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 7357) = 1/(7357 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-412833141 / 125000000) (-3302665123 / 1000000000) (Real.log (7357 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3979521983 / 1000000000) ≤ -Real.log (250000000000 / 13372864615971) ∧
    -Real.log (250000000000 / 13372864615971) ≤ (3979521989 / 1000000000) := by
  have h := checkLog_sound (w := (5372864615971 / 21372864615971)) (n := 12)
    (lo := (513786083 / 1000000000)) (hi := (128446521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13372864615971 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13372864615971 / 8000000000000) = 1/(250000000000 / 13372864615971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3979521983 / 1000000000) (3979521989 / 1000000000) (Real.log (13372864615971 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (13372864615971 / 250000000000) = -Real.log (250000000000 / 13372864615971) := by
    rw [show ((13372864615971 / 250000000000) : ℝ) = ((250000000000 / 13372864615971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3987490443 / 1000000000) ≤ -Real.log (100000000000 / 5391940577203) ∧
    -Real.log (100000000000 / 5391940577203) ≤ (3987490449 / 1000000000) := by
  have h := checkLog_sound (w := (2191940577203 / 8591940577203)) (n := 12)
    (lo := (521754543 / 1000000000)) (hi := (32609659 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5391940577203 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5391940577203 / 3200000000000) = 1/(100000000000 / 5391940577203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3987490443 / 1000000000) (3987490449 / 1000000000) (Real.log (5391940577203 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5391940577203 / 100000000000) = -Real.log (100000000000 / 5391940577203) := by
    rw [show ((5391940577203 / 100000000000) : ℝ) = ((100000000000 / 5391940577203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1984569087 / 500000000) ≤ -Real.log (250000000000 / 13234721810189) ∧
    -Real.log (250000000000 / 13234721810189) ≤ (198456909 / 50000000) := by
  have h := checkLog_sound (w := (5234721810189 / 21234721810189)) (n := 12)
    (lo := (251701137 / 500000000)) (hi := (20136091 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13234721810189 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13234721810189 / 8000000000000) = 1/(250000000000 / 13234721810189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1984569087 / 500000000) (198456909 / 50000000) (Real.log (13234721810189 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13234721810189 / 250000000000) = -Real.log (250000000000 / 13234721810189) := by
    rw [show ((13234721810189 / 250000000000) : ℝ) = ((250000000000 / 13234721810189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1988624279 / 500000000) ≤ -Real.log (500000000000 / 26684993883377) ∧
    -Real.log (500000000000 / 26684993883377) ≤ (994312141 / 250000000) := by
  have h := checkLog_sound (w := (10684993883377 / 42684993883377)) (n := 12)
    (lo := (255756329 / 500000000)) (hi := (511512659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26684993883377 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26684993883377 / 16000000000000) = 1/(500000000000 / 26684993883377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1988624279 / 500000000) (994312141 / 250000000) (Real.log (26684993883377 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (26684993883377 / 500000000000) = -Real.log (500000000000 / 26684993883377) := by
    rw [show ((26684993883377 / 500000000000) : ℝ) = ((500000000000 / 26684993883377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0104

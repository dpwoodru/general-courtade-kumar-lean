import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0078
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

theorem reflection_log_1_neg : (337785879 / 500000000) ≤ -Real.log (6400 / 12577) ∧
    -Real.log (6400 / 12577) ≤ (675571759 / 1000000000) := by
  have h := checkLog_sound (w := (6177 / 18977)) (n := 12)
    (lo := (337785879 / 500000000)) (hi := (675571759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12577 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12577 / 6400) = 1/(6400 / 12577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (337785879 / 500000000) (675571759 / 1000000000) (Real.log (12577 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12577 / 6400) = -Real.log (6400 / 12577) := by
    rw [show ((12577 / 6400) : ℝ) = ((6400 / 12577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (671376299 / 200000000) ≤ -Real.log (223 / 6400) ∧
    -Real.log (223 / 6400) ≤ (6713763 / 2000000) := by
  have h := checkLog_sound (w := (177 / 623)) (n := 12)
    (lo := (23371711 / 40000000)) (hi := (73036597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 223) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 223) = 1/(223 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6713763 / 2000000) (-671376299 / 200000000) (Real.log (223 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (84422863 / 125000000) ≤ -Real.log (51200 / 100597) ∧
    -Real.log (51200 / 100597) ≤ (135076581 / 200000000) := by
  have h := checkLog_sound (w := (49397 / 151797)) (n := 12)
    (lo := (84422863 / 125000000)) (hi := (135076581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100597 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100597 / 51200) = 1/(51200 / 100597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (84422863 / 125000000) (135076581 / 200000000) (Real.log (100597 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100597 / 51200) = -Real.log (51200 / 100597) := by
    rw [show ((100597 / 51200) : ℝ) = ((51200 / 100597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (669257517 / 200000000) ≤ -Real.log (1803 / 51200) ∧
    -Real.log (1803 / 51200) ≤ (334628759 / 100000000) := by
  have h := checkLog_sound (w := (1397 / 5003)) (n := 12)
    (lo := (114739773 / 200000000)) (hi := (286849433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1803) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1803) = 1/(1803 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-334628759 / 100000000) (-669257517 / 200000000) (Real.log (1803 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (328840953 / 500000000) ≤ -Real.log (3200 / 6177) ∧
    -Real.log (3200 / 6177) ≤ (657681907 / 1000000000) := by
  have h := checkLog_sound (w := (2977 / 9377)) (n := 12)
    (lo := (328840953 / 500000000)) (hi := (657681907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6177 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6177 / 3200) = 1/(3200 / 6177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (328840953 / 500000000) (657681907 / 1000000000) (Real.log (6177 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6177 / 3200) = -Real.log (3200 / 6177) := by
    rw [show ((6177 / 3200) : ℝ) = ((3200 / 6177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (532746863 / 200000000) ≤ -Real.log (223 / 3200) ∧
    -Real.log (223 / 3200) ≤ (2663734319 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 623)) (n := 12)
    (lo := (23371711 / 40000000)) (hi := (73036597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 223) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 223) = 1/(223 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2663734319 / 1000000000) (-532746863 / 200000000) (Real.log (223 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (328648671 / 500000000) ≤ -Real.log (25600 / 49397) ∧
    -Real.log (25600 / 49397) ≤ (657297343 / 1000000000) := by
  have h := checkLog_sound (w := (23797 / 74997)) (n := 12)
    (lo := (328648671 / 500000000)) (hi := (657297343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49397 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49397 / 25600) = 1/(25600 / 49397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (328648671 / 500000000) (657297343 / 1000000000) (Real.log (49397 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49397 / 25600) = -Real.log (25600 / 49397) := by
    rw [show ((49397 / 25600) : ℝ) = ((25600 / 49397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (530628081 / 200000000) ≤ -Real.log (1803 / 25600) ∧
    -Real.log (1803 / 25600) ≤ (2653140409 / 1000000000) := by
  have h := checkLog_sound (w := (1397 / 5003)) (n := 12)
    (lo := (114739773 / 200000000)) (hi := (286849433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1803) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1803) = 1/(1803 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2653140409 / 1000000000) (-530628081 / 200000000) (Real.log (1803 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (339218507 / 500000000) ≤ -Real.log (200000 / 394159) ∧
    -Real.log (200000 / 394159) ≤ (135687403 / 200000000) := by
  have h := checkLog_sound (w := (194159 / 594159)) (n := 12)
    (lo := (339218507 / 500000000)) (hi := (135687403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394159 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394159 / 200000) = 1/(200000 / 394159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (339218507 / 500000000) (135687403 / 200000000) (Real.log (394159 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (394159 / 200000) = -Real.log (200000 / 394159) := by
    rw [show ((394159 / 200000) : ℝ) = ((200000 / 394159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (883353837 / 250000000) ≤ -Real.log (5841 / 200000) ∧
    -Real.log (5841 / 200000) ≤ (1766707677 / 500000000) := by
  have h := checkLog_sound (w := (409 / 12091)) (n := 12)
    (lo := (8459931 / 125000000)) (hi := (67679449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5841) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5841) = 1/(5841 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1766707677 / 500000000) (-883353837 / 250000000) (Real.log (5841 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339292837 / 500000000) ≤ -Real.log (62500 / 123193) ∧
    -Real.log (62500 / 123193) ≤ (27143427 / 40000000) := by
  have h := checkLog_sound (w := (60693 / 185693)) (n := 12)
    (lo := (339292837 / 500000000)) (hi := (27143427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123193 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123193 / 62500) = 1/(62500 / 123193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339292837 / 500000000) (27143427 / 40000000) (Real.log (123193 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (123193 / 62500) = -Real.log (62500 / 123193) := by
    rw [show ((123193 / 62500) : ℝ) = ((62500 / 123193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1771749271 / 500000000) ≤ -Real.log (1807 / 62500) ∧
    -Real.log (1807 / 62500) ≤ (885874637 / 250000000) := by
  have h := checkLog_sound (w := (1169 / 30081)) (n := 12)
    (lo := (38881321 / 500000000)) (hi := (77762643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14456) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14456) = 1/(1807 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-885874637 / 250000000) (-1771749271 / 500000000) (Real.log (1807 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (678326393 / 1000000000) ≤ -Real.log (1000000 / 1970577) ∧
    -Real.log (1000000 / 1970577) ≤ (339163197 / 500000000) := by
  have h := checkLog_sound (w := (970577 / 2970577)) (n := 12)
    (lo := (678326393 / 1000000000)) (hi := (339163197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1970577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1970577 / 1000000) = 1/(1000000 / 1970577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (678326393 / 1000000000) (339163197 / 500000000) (Real.log (1970577 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1970577 / 1000000) = -Real.log (1000000 / 1970577) := by
    rw [show ((1970577 / 1000000) : ℝ) = ((1000000 / 1970577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1762989297 / 500000000) ≤ -Real.log (29423 / 1000000) ∧
    -Real.log (29423 / 1000000) ≤ (17629893 / 5000000) := by
  have h := checkLog_sound (w := (1827 / 60673)) (n := 12)
    (lo := (30121347 / 500000000)) (hi := (12048539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29423) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 29423) = 1/(29423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-17629893 / 5000000) (-1762989297 / 500000000) (Real.log (29423 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (339238803 / 500000000) ≤ -Real.log (8000 / 15767) ∧
    -Real.log (8000 / 15767) ≤ (678477607 / 1000000000) := by
  have h := checkLog_sound (w := (7767 / 23767)) (n := 12)
    (lo := (339238803 / 500000000)) (hi := (678477607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15767 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15767 / 8000) = 1/(8000 / 15767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (339238803 / 500000000) (678477607 / 1000000000) (Real.log (15767 / 8000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (15767 / 8000) = -Real.log (8000 / 15767) := by
    rw [show ((15767 / 8000) : ℝ) = ((8000 / 15767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (884039591 / 250000000) ≤ -Real.log (233 / 8000) ∧
    -Real.log (233 / 8000) ≤ (353615837 / 100000000) := by
  have h := checkLog_sound (w := (17 / 483)) (n := 12)
    (lo := (1100351 / 15625000)) (hi := (14084493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 233) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(250 / 233) = 1/(233 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-353615837 / 100000000) (-884039591 / 250000000) (Real.log (233 / 8000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2105926181 / 500000000) ≤ -Real.log (500000000000 / 33740712206813) ∧
    -Real.log (500000000000 / 33740712206813) ≤ (4211852369 / 1000000000) := by
  have h := checkLog_sound (w := (1740712206813 / 65740712206813)) (n := 12)
    (lo := (26484641 / 500000000)) (hi := (52969283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33740712206813 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33740712206813 / 32000000000000) = 1/(500000000000 / 33740712206813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2105926181 / 500000000) (4211852369 / 1000000000) (Real.log (33740712206813 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (33740712206813 / 500000000000) = -Real.log (500000000000 / 33740712206813) := by
    rw [show ((33740712206813 / 500000000000) : ℝ) = ((500000000000 / 33740712206813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (527760527 / 125000000) ≤ -Real.log (50000000000 / 3408771444383) ∧
    -Real.log (50000000000 / 3408771444383) ≤ (4222084223 / 1000000000) := by
  have h := checkLog_sound (w := (208771444383 / 6608771444383)) (n := 12)
    (lo := (3950071 / 62500000)) (hi := (63201137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3408771444383 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3408771444383 / 3200000000000) = 1/(50000000000 / 3408771444383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (527760527 / 125000000) (4222084223 / 1000000000) (Real.log (3408771444383 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3408771444383 / 50000000000) = -Real.log (50000000000 / 3408771444383) := by
    rw [show ((3408771444383 / 50000000000) : ℝ) = ((50000000000 / 3408771444383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4204304987 / 1000000000) ≤ -Real.log (500000000000 / 33487016959521) ∧
    -Real.log (500000000000 / 33487016959521) ≤ (2102152497 / 500000000) := by
  have h := checkLog_sound (w := (1487016959521 / 65487016959521)) (n := 12)
    (lo := (45421907 / 1000000000)) (hi := (11355477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33487016959521 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33487016959521 / 32000000000000) = 1/(500000000000 / 33487016959521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4204304987 / 1000000000) (2102152497 / 500000000) (Real.log (33487016959521 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (33487016959521 / 500000000000) = -Real.log (500000000000 / 33487016959521) := by
    rw [show ((33487016959521 / 500000000000) : ℝ) = ((500000000000 / 33487016959521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (421463597 / 100000000) ≤ -Real.log (250000000000 / 16917381974249) ∧
    -Real.log (250000000000 / 16917381974249) ≤ (4214635977 / 1000000000) := by
  have h := checkLog_sound (w := (917381974249 / 32917381974249)) (n := 12)
    (lo := (5575289 / 100000000)) (hi := (55752891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16917381974249 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(16917381974249 / 16000000000000) = 1/(250000000000 / 16917381974249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (421463597 / 100000000) (4214635977 / 1000000000) (Real.log (16917381974249 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16917381974249 / 250000000000) = -Real.log (250000000000 / 16917381974249) := by
    rw [show ((16917381974249 / 250000000000) : ℝ) = ((250000000000 / 16917381974249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0078

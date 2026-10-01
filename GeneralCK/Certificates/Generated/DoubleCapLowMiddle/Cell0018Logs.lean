import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0018
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

theorem reflection_log_1_neg : (682065497 / 1000000000) ≤ -Real.log (102400 / 202543) ∧
    -Real.log (102400 / 202543) ≤ (341032749 / 500000000) := by
  have h := checkLog_sound (w := (100143 / 304943)) (n := 12)
    (lo := (682065497 / 1000000000)) (hi := (341032749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202543 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202543 / 102400) = 1/(102400 / 202543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682065497 / 1000000000) (341032749 / 500000000) (Real.log (202543 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202543 / 102400) = -Real.log (102400 / 202543) := by
    rw [show ((202543 / 102400) : ℝ) = ((102400 / 202543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3814850211 / 1000000000) ≤ -Real.log (2257 / 102400) ∧
    -Real.log (2257 / 102400) ≤ (3814850217 / 1000000000) := by
  have h := checkLog_sound (w := (943 / 5457)) (n := 12)
    (lo := (349114311 / 1000000000)) (hi := (43639289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2257) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2257) = 1/(2257 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3814850217 / 1000000000) (-3814850211 / 1000000000) (Real.log (2257 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (136394337 / 200000000) ≤ -Real.log (25600 / 50631) ∧
    -Real.log (25600 / 50631) ≤ (340985843 / 500000000) := by
  have h := checkLog_sound (w := (25031 / 76231)) (n := 12)
    (lo := (136394337 / 200000000)) (hi := (340985843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50631 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50631 / 25600) = 1/(25600 / 50631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (136394337 / 200000000) (340985843 / 500000000) (Real.log (50631 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50631 / 25600) = -Real.log (25600 / 50631) := by
    rw [show ((50631 / 25600) : ℝ) = ((25600 / 50631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3806467193 / 1000000000) ≤ -Real.log (569 / 25600) ∧
    -Real.log (569 / 25600) ≤ (3806467199 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 1369)) (n := 12)
    (lo := (340731293 / 1000000000)) (hi := (170365647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 569) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 569) = 1/(569 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3806467199 / 1000000000) (-3806467193 / 1000000000) (Real.log (569 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41928727 / 62500000) ≤ -Real.log (51200 / 100143) ∧
    -Real.log (51200 / 100143) ≤ (670859633 / 1000000000) := by
  have h := checkLog_sound (w := (48943 / 151343)) (n := 12)
    (lo := (41928727 / 62500000)) (hi := (670859633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100143 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100143 / 51200) = 1/(51200 / 100143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41928727 / 62500000) (670859633 / 1000000000) (Real.log (100143 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100143 / 51200) = -Real.log (51200 / 100143) := by
    rw [show ((100143 / 51200) : ℝ) = ((51200 / 100143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3121703031 / 1000000000) ≤ -Real.log (2257 / 51200) ∧
    -Real.log (2257 / 51200) ≤ (780425759 / 250000000) := by
  have h := checkLog_sound (w := (943 / 5457)) (n := 12)
    (lo := (349114311 / 1000000000)) (hi := (43639289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2257) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2257) = 1/(2257 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-780425759 / 250000000) (-3121703031 / 1000000000) (Real.log (2257 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (134133977 / 200000000) ≤ -Real.log (12800 / 25031) ∧
    -Real.log (12800 / 25031) ≤ (335334943 / 500000000) := by
  have h := checkLog_sound (w := (12231 / 37831)) (n := 12)
    (lo := (134133977 / 200000000)) (hi := (335334943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25031 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25031 / 12800) = 1/(12800 / 25031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (134133977 / 200000000) (335334943 / 500000000) (Real.log (25031 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (25031 / 12800) = -Real.log (12800 / 25031) := by
    rw [show ((25031 / 12800) : ℝ) = ((12800 / 25031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3113320013 / 1000000000) ≤ -Real.log (569 / 12800) ∧
    -Real.log (569 / 12800) ≤ (1556660009 / 500000000) := by
  have h := checkLog_sound (w := (231 / 1369)) (n := 12)
    (lo := (340731293 / 1000000000)) (hi := (170365647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 569) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 569) = 1/(569 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1556660009 / 500000000) (-3113320013 / 1000000000) (Real.log (569 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170922021 / 250000000) ≤ -Real.log (1000000 / 1981171) ∧
    -Real.log (1000000 / 1981171) ≤ (136737617 / 200000000) := by
  have h := checkLog_sound (w := (981171 / 2981171)) (n := 12)
    (lo := (170922021 / 250000000)) (hi := (136737617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981171 / 1000000) = 1/(1000000 / 1981171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170922021 / 250000000) (136737617 / 200000000) (Real.log (1981171 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1981171 / 1000000) = -Real.log (1000000 / 1981171) := by
    rw [show ((1981171 / 1000000) : ℝ) = ((1000000 / 1981171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3972357041 / 1000000000) ≤ -Real.log (18829 / 1000000) ∧
    -Real.log (18829 / 1000000) ≤ (3972357047 / 1000000000) := by
  have h := checkLog_sound (w := (12421 / 50079)) (n := 12)
    (lo := (506621141 / 1000000000)) (hi := (253310571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18829) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18829) = 1/(18829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3972357047 / 1000000000) (-3972357041 / 1000000000) (Real.log (18829 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (683764803 / 1000000000) ≤ -Real.log (1000000 / 1981323) ∧
    -Real.log (1000000 / 1981323) ≤ (170941201 / 250000000) := by
  have h := checkLog_sound (w := (981323 / 2981323)) (n := 12)
    (lo := (683764803 / 1000000000)) (hi := (170941201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981323 / 1000000) = 1/(1000000 / 1981323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (683764803 / 1000000000) (170941201 / 250000000) (Real.log (1981323 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1981323 / 1000000) = -Real.log (1000000 / 1981323) := by
    rw [show ((1981323 / 1000000) : ℝ) = ((1000000 / 1981323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (796092491 / 200000000) ≤ -Real.log (18677 / 1000000) ∧
    -Real.log (18677 / 1000000) ≤ (3980462461 / 1000000000) := by
  have h := checkLog_sound (w := (12573 / 49927)) (n := 12)
    (lo := (102945311 / 200000000)) (hi := (128681639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18677) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18677) = 1/(18677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3980462461 / 1000000000) (-796092491 / 200000000) (Real.log (18677 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (683649217 / 1000000000) ≤ -Real.log (500000 / 990547) ∧
    -Real.log (500000 / 990547) ≤ (341824609 / 500000000) := by
  have h := checkLog_sound (w := (490547 / 1490547)) (n := 12)
    (lo := (683649217 / 1000000000)) (hi := (341824609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990547 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990547 / 500000) = 1/(500000 / 990547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (683649217 / 1000000000) (341824609 / 500000000) (Real.log (990547 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (990547 / 500000) = -Real.log (500000 / 990547) := by
    rw [show ((990547 / 500000) : ℝ) = ((500000 / 990547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (496034493 / 125000000) ≤ -Real.log (9453 / 500000) ∧
    -Real.log (9453 / 500000) ≤ (79365519 / 20000000) := by
  have h := checkLog_sound (w := (3086 / 12539)) (n := 12)
    (lo := (125635011 / 250000000)) (hi := (100508009 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9453) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9453) = 1/(9453 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-79365519 / 20000000) (-496034493 / 125000000) (Real.log (9453 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (170931611 / 250000000) ≤ -Real.log (1000000 / 1981247) ∧
    -Real.log (1000000 / 1981247) ≤ (136745289 / 200000000) := by
  have h := checkLog_sound (w := (981247 / 2981247)) (n := 12)
    (lo := (170931611 / 250000000)) (hi := (136745289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981247 / 1000000) = 1/(1000000 / 1981247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (170931611 / 250000000) (136745289 / 200000000) (Real.log (1981247 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1981247 / 1000000) = -Real.log (1000000 / 1981247) := by
    rw [show ((1981247 / 1000000) : ℝ) = ((1000000 / 1981247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (31065637 / 7812500) ≤ -Real.log (18753 / 1000000) ∧
    -Real.log (18753 / 1000000) ≤ (1988200771 / 500000000) := by
  have h := checkLog_sound (w := (12497 / 50003)) (n := 12)
    (lo := (127666409 / 250000000)) (hi := (510665637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18753) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18753) = 1/(18753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1988200771 / 500000000) (-31065637 / 7812500) (Real.log (18753 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (37248361 / 8000000) ≤ -Real.log (250000000000 / 26304782516331) ∧
    -Real.log (250000000000 / 26304782516331) ≤ (1164011283 / 250000000) := by
  have h := checkLog_sound (w := (10304782516331 / 42304782516331)) (n := 12)
    (lo := (99432409 / 200000000)) (hi := (248581023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26304782516331 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(26304782516331 / 16000000000000) = 1/(250000000000 / 26304782516331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (37248361 / 8000000) (1164011283 / 250000000) (Real.log (26304782516331 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (26304782516331 / 250000000000) = -Real.log (250000000000 / 26304782516331) := by
    rw [show ((26304782516331 / 250000000000) : ℝ) = ((250000000000 / 26304782516331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2332113629 / 500000000) ≤ -Real.log (500000000000 / 53041789366601) ∧
    -Real.log (500000000000 / 53041789366601) ≤ (932845453 / 200000000) := by
  have h := checkLog_sound (w := (21041789366601 / 85041789366601)) (n := 12)
    (lo := (252672089 / 500000000)) (hi := (505344179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53041789366601 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(53041789366601 / 32000000000000) = 1/(500000000000 / 53041789366601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2332113629 / 500000000) (932845453 / 200000000) (Real.log (53041789366601 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (53041789366601 / 500000000000) = -Real.log (500000000000 / 53041789366601) := by
    rw [show ((53041789366601 / 500000000000) : ℝ) = ((500000000000 / 53041789366601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (116298129 / 25000000) ≤ -Real.log (500000000000 / 52393261398497) ∧
    -Real.log (500000000000 / 52393261398497) ≤ (4651925167 / 1000000000) := by
  have h := checkLog_sound (w := (20393261398497 / 84393261398497)) (n := 12)
    (lo := (3081513 / 6250000)) (hi := (493042081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52393261398497 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52393261398497 / 32000000000000) = 1/(500000000000 / 52393261398497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (116298129 / 25000000) (4651925167 / 1000000000) (Real.log (52393261398497 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (52393261398497 / 500000000000) = -Real.log (500000000000 / 52393261398497) := by
    rw [show ((52393261398497 / 500000000000) : ℝ) = ((500000000000 / 52393261398497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (233006399 / 50000000) ≤ -Real.log (100000000000 / 10564960273023) ∧
    -Real.log (100000000000 / 10564960273023) ≤ (4660127987 / 1000000000) := by
  have h := checkLog_sound (w := (4164960273023 / 16964960273023)) (n := 12)
    (lo := (5012449 / 10000000)) (hi := (501244901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10564960273023 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10564960273023 / 6400000000000) = 1/(100000000000 / 10564960273023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (233006399 / 50000000) (4660127987 / 1000000000) (Real.log (10564960273023 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10564960273023 / 100000000000) = -Real.log (100000000000 / 10564960273023) := by
    rw [show ((10564960273023 / 100000000000) : ℝ) = ((100000000000 / 10564960273023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0018

import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0083
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

theorem reflection_log_1_neg : (84328391 / 125000000) ≤ -Real.log (51200 / 100521) ∧
    -Real.log (51200 / 100521) ≤ (674627129 / 1000000000) := by
  have h := checkLog_sound (w := (49321 / 151721)) (n := 12)
    (lo := (84328391 / 125000000)) (hi := (674627129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100521 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100521 / 51200) = 1/(51200 / 100521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (84328391 / 125000000) (674627129 / 1000000000) (Real.log (100521 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100521 / 51200) = -Real.log (51200 / 100521) := by
    rw [show ((100521 / 51200) : ℝ) = ((51200 / 100521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3304999809 / 1000000000) ≤ -Real.log (1879 / 51200) ∧
    -Real.log (1879 / 51200) ≤ (1652499907 / 500000000) := by
  have h := checkLog_sound (w := (1321 / 5079)) (n := 12)
    (lo := (532411089 / 1000000000)) (hi := (53241109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1879) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1879) = 1/(1879 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1652499907 / 500000000) (-3304999809 / 1000000000) (Real.log (1879 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (134887619 / 200000000) ≤ -Real.log (25600 / 50251) ∧
    -Real.log (25600 / 50251) ≤ (42152381 / 62500000) := by
  have h := checkLog_sound (w := (24651 / 75851)) (n := 12)
    (lo := (134887619 / 200000000)) (hi := (42152381 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50251 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50251 / 25600) = 1/(25600 / 50251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (134887619 / 200000000) (42152381 / 62500000) (Real.log (50251 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50251 / 25600) = -Real.log (25600 / 50251) := by
    rw [show ((50251 / 25600) : ℝ) = ((25600 / 50251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3294938829 / 1000000000) ≤ -Real.log (949 / 25600) ∧
    -Real.log (949 / 25600) ≤ (1647469417 / 500000000) := by
  have h := checkLog_sound (w := (651 / 2549)) (n := 12)
    (lo := (522350109 / 1000000000)) (hi := (52235011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 949) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 949) = 1/(949 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1647469417 / 500000000) (-3294938829 / 1000000000) (Real.log (949 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (327878801 / 500000000) ≤ -Real.log (25600 / 49321) ∧
    -Real.log (25600 / 49321) ≤ (655757603 / 1000000000) := by
  have h := checkLog_sound (w := (23721 / 74921)) (n := 12)
    (lo := (327878801 / 500000000)) (hi := (655757603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49321 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49321 / 25600) = 1/(25600 / 49321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (327878801 / 500000000) (655757603 / 1000000000) (Real.log (49321 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49321 / 25600) = -Real.log (25600 / 49321) := by
    rw [show ((49321 / 25600) : ℝ) = ((25600 / 49321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2611852629 / 1000000000) ≤ -Real.log (1879 / 25600) ∧
    -Real.log (1879 / 25600) ≤ (2611852633 / 1000000000) := by
  have h := checkLog_sound (w := (1321 / 5079)) (n := 12)
    (lo := (532411089 / 1000000000)) (hi := (53241109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1879) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1879) = 1/(1879 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2611852633 / 1000000000) (-2611852629 / 1000000000) (Real.log (1879 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (81921537 / 125000000) ≤ -Real.log (12800 / 24651) ∧
    -Real.log (12800 / 24651) ≤ (655372297 / 1000000000) := by
  have h := checkLog_sound (w := (11851 / 37451)) (n := 12)
    (lo := (81921537 / 125000000)) (hi := (655372297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24651 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24651 / 12800) = 1/(12800 / 24651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (81921537 / 125000000) (655372297 / 1000000000) (Real.log (24651 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24651 / 12800) = -Real.log (12800 / 24651) := by
    rw [show ((24651 / 12800) : ℝ) = ((12800 / 24651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2601791649 / 1000000000) ≤ -Real.log (949 / 12800) ∧
    -Real.log (949 / 12800) ≤ (2601791653 / 1000000000) := by
  have h := checkLog_sound (w := (651 / 2549)) (n := 12)
    (lo := (522350109 / 1000000000)) (hi := (52235011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 949) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 949) = 1/(949 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2601791653 / 1000000000) (-2601791649 / 1000000000) (Real.log (949 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (677698461 / 1000000000) ≤ -Real.log (50000 / 98467) ∧
    -Real.log (50000 / 98467) ≤ (338849231 / 500000000) := by
  have h := checkLog_sound (w := (48467 / 148467)) (n := 12)
    (lo := (677698461 / 1000000000)) (hi := (338849231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98467 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98467 / 50000) = 1/(50000 / 98467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (677698461 / 1000000000) (338849231 / 500000000) (Real.log (98467 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (98467 / 50000) = -Real.log (50000 / 98467) := by
    rw [show ((98467 / 50000) : ℝ) = ((50000 / 98467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1742398201 / 500000000) ≤ -Real.log (1533 / 50000) ∧
    -Real.log (1533 / 50000) ≤ (435599551 / 125000000) := by
  have h := checkLog_sound (w := (59 / 6191)) (n := 12)
    (lo := (9530251 / 500000000)) (hi := (19060503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3066) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 3066) = 1/(1533 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-435599551 / 125000000) (-1742398201 / 500000000) (Real.log (1533 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135569243 / 200000000) ≤ -Real.log (1000000 / 1969631) ∧
    -Real.log (1000000 / 1969631) ≤ (84730777 / 125000000) := by
  have h := checkLog_sound (w := (969631 / 2969631)) (n := 12)
    (lo := (135569243 / 200000000)) (hi := (84730777 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969631 / 1000000) = 1/(1000000 / 1969631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135569243 / 200000000) (84730777 / 125000000) (Real.log (1969631 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1969631 / 1000000) = -Real.log (1000000 / 1969631) := by
    rw [show ((1969631 / 1000000) : ℝ) = ((1000000 / 1969631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (873583231 / 250000000) ≤ -Real.log (30369 / 1000000) ∧
    -Real.log (30369 / 1000000) ≤ (349433293 / 100000000) := by
  have h := checkLog_sound (w := (881 / 61619)) (n := 12)
    (lo := (893657 / 31250000)) (hi := (1143881 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30369) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30369) = 1/(30369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-349433293 / 100000000) (-873583231 / 250000000) (Real.log (30369 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (338787277 / 500000000) ≤ -Real.log (125000 / 246137) ∧
    -Real.log (125000 / 246137) ≤ (135514911 / 200000000) := by
  have h := checkLog_sound (w := (121137 / 371137)) (n := 12)
    (lo := (338787277 / 500000000)) (hi := (135514911 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246137 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246137 / 125000) = 1/(125000 / 246137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (338787277 / 500000000) (135514911 / 200000000) (Real.log (246137 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (246137 / 125000) = -Real.log (125000 / 246137) := by
    rw [show ((246137 / 125000) : ℝ) = ((125000 / 246137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69537393 / 20000000) ≤ -Real.log (3863 / 125000) ∧
    -Real.log (3863 / 125000) ≤ (434608707 / 125000000) := by
  have h := checkLog_sound (w := (173 / 31077)) (n := 12)
    (lo := (8907 / 800000)) (hi := (11133751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15452) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 15452) = 1/(3863 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-434608707 / 125000000) (-69537393 / 20000000) (Real.log (3863 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (677725373 / 1000000000) ≤ -Real.log (1000000 / 1969393) ∧
    -Real.log (1000000 / 1969393) ≤ (338862687 / 500000000) := by
  have h := checkLog_sound (w := (969393 / 2969393)) (n := 12)
    (lo := (677725373 / 1000000000)) (hi := (338862687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969393 / 1000000) = 1/(1000000 / 1969393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (677725373 / 1000000000) (338862687 / 500000000) (Real.log (1969393 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1969393 / 1000000) = -Real.log (1000000 / 1969393) := by
    rw [show ((1969393 / 1000000) : ℝ) = ((1000000 / 1969393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (697305307 / 200000000) ≤ -Real.log (30607 / 1000000) ∧
    -Real.log (30607 / 1000000) ≤ (3486526541 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 61857)) (n := 12)
    (lo := (4158127 / 200000000)) (hi := (5197659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30607) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30607) = 1/(30607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3486526541 / 1000000000) (-697305307 / 200000000) (Real.log (30607 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4162494863 / 1000000000) ≤ -Real.log (500000000000 / 32115786040443) ∧
    -Real.log (500000000000 / 32115786040443) ≤ (416249487 / 100000000) := by
  have h := checkLog_sound (w := (115786040443 / 64115786040443)) (n := 12)
    (lo := (3611783 / 1000000000)) (hi := (451473 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32115786040443 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32115786040443 / 32000000000000) = 1/(500000000000 / 32115786040443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4162494863 / 1000000000) (416249487 / 100000000) (Real.log (32115786040443 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (32115786040443 / 500000000000) = -Real.log (500000000000 / 32115786040443) := by
    rw [show ((32115786040443 / 500000000000) : ℝ) = ((500000000000 / 32115786040443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4172179139 / 1000000000) ≤ -Real.log (500000000000 / 32428315058119) ∧
    -Real.log (500000000000 / 32428315058119) ≤ (2086089573 / 500000000) := by
  have h := checkLog_sound (w := (428315058119 / 64428315058119)) (n := 12)
    (lo := (13296059 / 1000000000)) (hi := (664803 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32428315058119 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32428315058119 / 32000000000000) = 1/(500000000000 / 32428315058119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4172179139 / 1000000000) (2086089573 / 500000000) (Real.log (32428315058119 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (32428315058119 / 500000000000) = -Real.log (500000000000 / 32428315058119) := by
    rw [show ((32428315058119 / 500000000000) : ℝ) = ((500000000000 / 32428315058119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (830888841 / 200000000) ≤ -Real.log (500000000000 / 31858270774009) ∧
    -Real.log (500000000000 / 31858270774009) ≤ (4154444211 / 1000000000) := by
  have h := checkLog_sound (w := (15858270774009 / 47858270774009)) (n := 12)
    (lo := (137741661 / 200000000)) (hi := (344354153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31858270774009 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31858270774009 / 16000000000000) = 1/(500000000000 / 31858270774009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (830888841 / 200000000) (4154444211 / 1000000000) (Real.log (31858270774009 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (31858270774009 / 500000000000) = -Real.log (500000000000 / 31858270774009) := by
    rw [show ((31858270774009 / 500000000000) : ℝ) = ((500000000000 / 31858270774009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1041062977 / 250000000) ≤ -Real.log (250000000000 / 16086132257327) ∧
    -Real.log (250000000000 / 16086132257327) ≤ (832850383 / 200000000) := by
  have h := checkLog_sound (w := (86132257327 / 32086132257327)) (n := 12)
    (lo := (1342207 / 250000000)) (hi := (5368829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16086132257327 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(16086132257327 / 16000000000000) = 1/(250000000000 / 16086132257327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1041062977 / 250000000) (832850383 / 200000000) (Real.log (16086132257327 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16086132257327 / 250000000000) = -Real.log (250000000000 / 16086132257327) := by
    rw [show ((16086132257327 / 250000000000) : ℝ) = ((250000000000 / 16086132257327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0083

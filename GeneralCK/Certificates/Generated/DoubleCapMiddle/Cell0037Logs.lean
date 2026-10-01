import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0037
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

theorem reflection_log_1_neg : (24058967 / 62500000) ≤ -Real.log (1280 / 1881) ∧
    -Real.log (1280 / 1881) ≤ (384943473 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 3161)) (n := 12)
    (lo := (24058967 / 62500000)) (hi := (384943473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1881 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1881 / 1280) = 1/(1280 / 1881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24058967 / 62500000) (384943473 / 1000000000) (Real.log (1881 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1881 / 1280) = -Real.log (1280 / 1881) := by
    rw [show ((1881 / 1280) : ℝ) = ((1280 / 1881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (633994229 / 1000000000) ≤ -Real.log (679 / 1280) ∧
    -Real.log (679 / 1280) ≤ (63399423 / 100000000) := by
  have h := checkLog_sound (w := (601 / 1959)) (n := 12)
    (lo := (633994229 / 1000000000)) (hi := (63399423 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 679) = 1/(679 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-63399423 / 100000000) (-633994229 / 1000000000) (Real.log (679 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (192072853 / 500000000) ≤ -Real.log (2560 / 3759) ∧
    -Real.log (2560 / 3759) ≤ (384145707 / 1000000000) := by
  have h := checkLog_sound (w := (1199 / 6319)) (n := 12)
    (lo := (192072853 / 500000000)) (hi := (384145707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3759 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3759 / 2560) = 1/(2560 / 3759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (192072853 / 500000000) (384145707 / 1000000000) (Real.log (3759 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3759 / 2560) = -Real.log (2560 / 3759) := by
    rw [show ((3759 / 2560) : ℝ) = ((2560 / 3759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (315893767 / 500000000) ≤ -Real.log (1361 / 2560) ∧
    -Real.log (1361 / 2560) ≤ (126357507 / 200000000) := by
  have h := checkLog_sound (w := (1199 / 3921)) (n := 12)
    (lo := (315893767 / 500000000)) (hi := (126357507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1361) = 1/(1361 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-126357507 / 200000000) (-315893767 / 500000000) (Real.log (1361 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10346947 / 15625000) ≤ -Real.log (640 / 1241) ∧
    -Real.log (640 / 1241) ≤ (662204609 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 1881)) (n := 12)
    (lo := (10346947 / 15625000)) (hi := (662204609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241 / 640) = 1/(640 / 1241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (10346947 / 15625000) (662204609 / 1000000000) (Real.log (1241 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1241 / 640) = -Real.log (640 / 1241) := by
    rw [show ((1241 / 640) : ℝ) = ((640 / 1241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2797906527 / 1000000000) ≤ -Real.log (39 / 640) ∧
    -Real.log (39 / 640) ≤ (699476633 / 250000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 39) = 1/(39 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-699476633 / 250000000) (-2797906527 / 1000000000) (Real.log (39 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (26439807 / 40000000) ≤ -Real.log (1280 / 2479) ∧
    -Real.log (1280 / 2479) ≤ (82624397 / 125000000) := by
  have h := checkLog_sound (w := (1199 / 3759)) (n := 12)
    (lo := (26439807 / 40000000)) (hi := (82624397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2479 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2479 / 1280) = 1/(1280 / 2479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (26439807 / 40000000) (82624397 / 125000000) (Real.log (2479 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2479 / 1280) = -Real.log (1280 / 2479) := by
    rw [show ((2479 / 1280) : ℝ) = ((1280 / 2479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (13800831 / 5000000) ≤ -Real.log (81 / 1280) ∧
    -Real.log (81 / 1280) ≤ (690041551 / 250000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 81) = 1/(81 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-690041551 / 250000000) (-13800831 / 5000000) (Real.log (81 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (534614999 / 1000000000) ≤ -Real.log (1000000 / 1706791) ∧
    -Real.log (1000000 / 1706791) ≤ (106923 / 200000) := by
  have h := checkLog_sound (w := (706791 / 2706791)) (n := 12)
    (lo := (534614999 / 1000000000)) (hi := (106923 / 200000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1706791 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1706791 / 1000000) = 1/(1000000 / 1706791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (534614999 / 1000000000) (106923 / 200000) (Real.log (1706791 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1706791 / 1000000) = -Real.log (1000000 / 1706791) := by
    rw [show ((1706791 / 1000000) : ℝ) = ((1000000 / 1706791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1226869613 / 1000000000) ≤ -Real.log (293209 / 1000000) ∧
    -Real.log (293209 / 1000000) ≤ (245373923 / 200000000) := by
  have h := checkLog_sound (w := (206791 / 793209)) (n := 12)
    (lo := (533722433 / 1000000000)) (hi := (266861217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 293209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 293209) = 1/(293209 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-245373923 / 200000000) (-1226869613 / 1000000000) (Real.log (293209 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16748509 / 31250000) ≤ -Real.log (40000 / 68363) ∧
    -Real.log (40000 / 68363) ≤ (535952289 / 1000000000) := by
  have h := checkLog_sound (w := (28363 / 108363)) (n := 12)
    (lo := (16748509 / 31250000)) (hi := (535952289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68363 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68363 / 40000) = 1/(40000 / 68363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16748509 / 31250000) (535952289 / 1000000000) (Real.log (68363 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (68363 / 40000) = -Real.log (40000 / 68363) := by
    rw [show ((68363 / 40000) : ℝ) = ((40000 / 68363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (77168111 / 62500000) ≤ -Real.log (11637 / 40000) ∧
    -Real.log (11637 / 40000) ≤ (617344889 / 500000000) := by
  have h := checkLog_sound (w := (8363 / 31637)) (n := 12)
    (lo := (135385649 / 250000000)) (hi := (541542597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 11637) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 11637) = 1/(11637 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-617344889 / 500000000) (-77168111 / 62500000) (Real.log (11637 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (456542179 / 1000000000) ≤ -Real.log (500000 / 789303) ∧
    -Real.log (500000 / 789303) ≤ (22827109 / 50000000) := by
  have h := checkLog_sound (w := (289303 / 1289303)) (n := 12)
    (lo := (456542179 / 1000000000)) (hi := (22827109 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789303 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789303 / 500000) = 1/(500000 / 789303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (456542179 / 1000000000) (22827109 / 50000000) (Real.log (789303 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (789303 / 500000) = -Real.log (500000 / 789303) := by
    rw [show ((789303 / 500000) : ℝ) = ((500000 / 789303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (172837403 / 200000000) ≤ -Real.log (210697 / 500000) ∧
    -Real.log (210697 / 500000) ≤ (864187017 / 1000000000) := by
  have h := checkLog_sound (w := (39303 / 460697)) (n := 12)
    (lo := (34207967 / 200000000)) (hi := (42759959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 210697) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 210697) = 1/(210697 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-864187017 / 1000000000) (-172837403 / 200000000) (Real.log (210697 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (458086653 / 1000000000) ≤ -Real.log (500000 / 790523) ∧
    -Real.log (500000 / 790523) ≤ (229043327 / 500000000) := by
  have h := checkLog_sound (w := (290523 / 1290523)) (n := 12)
    (lo := (458086653 / 1000000000)) (hi := (229043327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((790523 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(790523 / 500000) = 1/(500000 / 790523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (458086653 / 1000000000) (229043327 / 500000000) (Real.log (790523 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (790523 / 500000) = -Real.log (500000 / 790523) := by
    rw [show ((790523 / 500000) : ℝ) = ((500000 / 790523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (869994149 / 1000000000) ≤ -Real.log (209477 / 500000) ∧
    -Real.log (209477 / 500000) ≤ (869994151 / 1000000000) := by
  have h := checkLog_sound (w := (40523 / 459477)) (n := 12)
    (lo := (176846969 / 1000000000)) (hi := (17684697 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 209477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 209477) = 1/(209477 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-869994151 / 1000000000) (-869994149 / 1000000000) (Real.log (209477 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1761484611 / 1000000000) ≤ -Real.log (250000000000 / 1455268255749) ∧
    -Real.log (250000000000 / 1455268255749) ≤ (880742307 / 500000000) := by
  have h := checkLog_sound (w := (455268255749 / 2455268255749)) (n := 12)
    (lo := (375190251 / 1000000000)) (hi := (93797563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1455268255749 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1455268255749 / 1000000000000) = 1/(250000000000 / 1455268255749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1761484611 / 1000000000) (880742307 / 500000000) (Real.log (1455268255749 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1455268255749 / 250000000000) = -Real.log (250000000000 / 1455268255749) := by
    rw [show ((1455268255749 / 250000000000) : ℝ) = ((250000000000 / 1455268255749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (110665129 / 62500000) ≤ -Real.log (500000000000 / 2937312021999) ∧
    -Real.log (500000000000 / 2937312021999) ≤ (1770642067 / 1000000000) := by
  have h := checkLog_sound (w := (937312021999 / 4937312021999)) (n := 12)
    (lo := (48043463 / 125000000)) (hi := (76869541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2937312021999 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2937312021999 / 2000000000000) = 1/(500000000000 / 2937312021999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (110665129 / 62500000) (1770642067 / 1000000000) (Real.log (2937312021999 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2937312021999 / 500000000000) = -Real.log (500000000000 / 2937312021999) := by
    rw [show ((2937312021999 / 500000000000) : ℝ) = ((500000000000 / 2937312021999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (660364597 / 500000000) ≤ -Real.log (500000000000 / 1873076028609) ∧
    -Real.log (500000000000 / 1873076028609) ≤ (330182299 / 250000000) := by
  have h := checkLog_sound (w := (873076028609 / 2873076028609)) (n := 12)
    (lo := (313791007 / 500000000)) (hi := (125516403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1873076028609 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1873076028609 / 1000000000000) = 1/(500000000000 / 1873076028609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (660364597 / 500000000) (330182299 / 250000000) (Real.log (1873076028609 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1873076028609 / 500000000000) = -Real.log (500000000000 / 1873076028609) := by
    rw [show ((1873076028609 / 500000000000) : ℝ) = ((500000000000 / 1873076028609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1328080803 / 1000000000) ≤ -Real.log (500000000000 / 1886896890829) ∧
    -Real.log (500000000000 / 1886896890829) ≤ (265616161 / 200000000) := by
  have h := checkLog_sound (w := (886896890829 / 2886896890829)) (n := 12)
    (lo := (634933623 / 1000000000)) (hi := (79366703 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1886896890829 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1886896890829 / 1000000000000) = 1/(500000000000 / 1886896890829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1328080803 / 1000000000) (265616161 / 200000000) (Real.log (1886896890829 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1886896890829 / 500000000000) = -Real.log (500000000000 / 1886896890829) := by
    rw [show ((1886896890829 / 500000000000) : ℝ) = ((500000000000 / 1886896890829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0037

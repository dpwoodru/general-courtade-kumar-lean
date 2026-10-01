import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0125
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

theorem reflection_log_1_neg : (156092059 / 500000000) ≤ -Real.log (1280 / 1749) ∧
    -Real.log (1280 / 1749) ≤ (312184119 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 3029)) (n := 12)
    (lo := (156092059 / 500000000)) (hi := (312184119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1749 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1749 / 1280) = 1/(1280 / 1749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (156092059 / 500000000) (312184119 / 1000000000) (Real.log (1749 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1749 / 1280) = -Real.log (1280 / 1749) := by
    rw [show ((1749 / 1280) : ℝ) = ((1280 / 1749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (228173651 / 500000000) ≤ -Real.log (811 / 1280) ∧
    -Real.log (811 / 1280) ≤ (456347303 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 2091)) (n := 12)
    (lo := (228173651 / 500000000)) (hi := (456347303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 811) = 1/(811 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-456347303 / 1000000000) (-228173651 / 500000000) (Real.log (811 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (311326117 / 1000000000) ≤ -Real.log (512 / 699) ∧
    -Real.log (512 / 699) ≤ (155663059 / 500000000) := by
  have h := checkLog_sound (w := (187 / 1211)) (n := 12)
    (lo := (311326117 / 1000000000)) (hi := (155663059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699 / 512) = 1/(512 / 699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (311326117 / 1000000000) (155663059 / 500000000) (Real.log (699 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (699 / 512) = -Real.log (512 / 699) := by
    rw [show ((699 / 512) : ℝ) = ((512 / 699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (227249721 / 500000000) ≤ -Real.log (325 / 512) ∧
    -Real.log (325 / 512) ≤ (454499443 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 837)) (n := 12)
    (lo := (227249721 / 500000000)) (hi := (454499443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 325) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 325) = 1/(325 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-454499443 / 1000000000) (-227249721 / 500000000) (Real.log (325 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (54974581 / 100000000) ≤ -Real.log (640 / 1109) ∧
    -Real.log (640 / 1109) ≤ (549745811 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 1749)) (n := 12)
    (lo := (54974581 / 100000000)) (hi := (549745811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1109 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1109 / 640) = 1/(640 / 1109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (54974581 / 100000000) (549745811 / 1000000000) (Real.log (1109 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1109 / 640) = -Real.log (640 / 1109) := by
    rw [show ((1109 / 640) : ℝ) = ((640 / 1109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1319804619 / 1000000000) ≤ -Real.log (171 / 640) ∧
    -Real.log (171 / 640) ≤ (1319804621 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 171) = 1/(171 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1319804621 / 1000000000) (-1319804619 / 1000000000) (Real.log (171 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (21935693 / 40000000) ≤ -Real.log (256 / 443) ∧
    -Real.log (256 / 443) ≤ (274196163 / 500000000) := by
  have h := checkLog_sound (w := (187 / 699)) (n := 12)
    (lo := (21935693 / 40000000)) (hi := (274196163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((443 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(443 / 256) = 1/(256 / 443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (21935693 / 40000000) (274196163 / 500000000) (Real.log (443 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (443 / 256) = -Real.log (256 / 443) := by
    rw [show ((443 / 256) : ℝ) = ((256 / 443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1311070939 / 1000000000) ≤ -Real.log (69 / 256) ∧
    -Real.log (69 / 256) ≤ (1311070941 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 197)) (n := 12)
    (lo := (617923759 / 1000000000)) (hi := (7724047 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 69) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 69) = 1/(69 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1311070941 / 1000000000) (-1311070939 / 1000000000) (Real.log (69 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (213186503 / 500000000) ≤ -Real.log (250000 / 382923) ∧
    -Real.log (250000 / 382923) ≤ (426373007 / 1000000000) := by
  have h := checkLog_sound (w := (132923 / 632923)) (n := 12)
    (lo := (213186503 / 500000000)) (hi := (426373007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382923 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382923 / 250000) = 1/(250000 / 382923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (213186503 / 500000000) (426373007 / 1000000000) (Real.log (382923 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (382923 / 250000) = -Real.log (250000 / 382923) := by
    rw [show ((382923 / 250000) : ℝ) = ((250000 / 382923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (758629079 / 1000000000) ≤ -Real.log (117077 / 250000) ∧
    -Real.log (117077 / 250000) ≤ (758629081 / 1000000000) := by
  have h := checkLog_sound (w := (7923 / 242077)) (n := 12)
    (lo := (65481899 / 1000000000)) (hi := (654819 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 117077) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 117077) = 1/(117077 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-758629081 / 1000000000) (-758629079 / 1000000000) (Real.log (117077 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (427574223 / 1000000000) ≤ -Real.log (1000000 / 1533533) ∧
    -Real.log (1000000 / 1533533) ≤ (26723389 / 62500000) := by
  have h := checkLog_sound (w := (533533 / 2533533)) (n := 12)
    (lo := (427574223 / 1000000000)) (hi := (26723389 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1533533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1533533 / 1000000) = 1/(1000000 / 1533533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (427574223 / 1000000000) (26723389 / 62500000) (Real.log (1533533 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1533533 / 1000000) = -Real.log (1000000 / 1533533) := by
    rw [show ((1533533 / 1000000) : ℝ) = ((1000000 / 1533533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (95321 / 125000) ≤ -Real.log (466467 / 1000000) ∧
    -Real.log (466467 / 1000000) ≤ (381284001 / 500000000) := by
  have h := checkLog_sound (w := (33533 / 966467)) (n := 12)
    (lo := (3471041 / 50000000)) (hi := (69420821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 466467) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 466467) = 1/(466467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-381284001 / 500000000) (-95321 / 125000) (Real.log (466467 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (85493021 / 250000000) ≤ -Real.log (1000000 / 1407721) ∧
    -Real.log (1000000 / 1407721) ≤ (68394417 / 200000000) := by
  have h := checkLog_sound (w := (407721 / 2407721)) (n := 12)
    (lo := (85493021 / 250000000)) (hi := (68394417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1407721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1407721 / 1000000) = 1/(1000000 / 1407721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (85493021 / 250000000) (68394417 / 200000000) (Real.log (1407721 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1407721 / 1000000) = -Real.log (1000000 / 1407721) := by
    rw [show ((1407721 / 1000000) : ℝ) = ((1000000 / 1407721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (523777471 / 1000000000) ≤ -Real.log (592279 / 1000000) ∧
    -Real.log (592279 / 1000000) ≤ (8184023 / 15625000) := by
  have h := checkLog_sound (w := (407721 / 1592279)) (n := 12)
    (lo := (523777471 / 1000000000)) (hi := (8184023 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 592279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 592279) = 1/(592279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8184023 / 15625000) (-523777471 / 1000000000) (Real.log (592279 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (85785699 / 250000000) ≤ -Real.log (100000 / 140937) ∧
    -Real.log (100000 / 140937) ≤ (343142797 / 1000000000) := by
  have h := checkLog_sound (w := (40937 / 240937)) (n := 12)
    (lo := (85785699 / 250000000)) (hi := (343142797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140937 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140937 / 100000) = 1/(100000 / 140937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (85785699 / 250000000) (343142797 / 1000000000) (Real.log (140937 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (140937 / 100000) = -Real.log (100000 / 140937) := by
    rw [show ((140937 / 100000) : ℝ) = ((100000 / 140937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (105313103 / 200000000) ≤ -Real.log (59063 / 100000) ∧
    -Real.log (59063 / 100000) ≤ (131641379 / 250000000) := by
  have h := checkLog_sound (w := (40937 / 159063)) (n := 12)
    (lo := (105313103 / 200000000)) (hi := (131641379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 59063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 59063) = 1/(59063 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-131641379 / 250000000) (-105313103 / 200000000) (Real.log (59063 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (592501043 / 500000000) ≤ -Real.log (50000000000 / 163534682303) ∧
    -Real.log (50000000000 / 163534682303) ≤ (148125261 / 125000000) := by
  have h := checkLog_sound (w := (63534682303 / 263534682303)) (n := 12)
    (lo := (245927453 / 500000000)) (hi := (491854907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163534682303 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(163534682303 / 100000000000) = 1/(50000000000 / 163534682303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (592501043 / 500000000) (148125261 / 125000000) (Real.log (163534682303 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (163534682303 / 50000000000) = -Real.log (50000000000 / 163534682303) := by
    rw [show ((163534682303 / 50000000000) : ℝ) = ((50000000000 / 163534682303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1190142223 / 1000000000) ≤ -Real.log (100000000000 / 328754874407) ∧
    -Real.log (100000000000 / 328754874407) ≤ (47605689 / 40000000) := by
  have h := checkLog_sound (w := (128754874407 / 528754874407)) (n := 12)
    (lo := (496995043 / 1000000000)) (hi := (124248761 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328754874407 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(328754874407 / 200000000000) = 1/(100000000000 / 328754874407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1190142223 / 1000000000) (47605689 / 40000000) (Real.log (328754874407 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (328754874407 / 100000000000) = -Real.log (100000000000 / 328754874407) := by
    rw [show ((328754874407 / 100000000000) : ℝ) = ((100000000000 / 328754874407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (173149911 / 200000000) ≤ -Real.log (250000000000 / 594196738361) ∧
    -Real.log (250000000000 / 594196738361) ≤ (865749557 / 1000000000) := by
  have h := checkLog_sound (w := (94196738361 / 1094196738361)) (n := 12)
    (lo := (1380819 / 8000000)) (hi := (21575297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594196738361 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(594196738361 / 500000000000) = 1/(250000000000 / 594196738361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (173149911 / 200000000) (865749557 / 1000000000) (Real.log (594196738361 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (594196738361 / 250000000000) = -Real.log (250000000000 / 594196738361) := by
    rw [show ((594196738361 / 250000000000) : ℝ) = ((250000000000 / 594196738361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (86970831 / 100000000) ≤ -Real.log (250000000000 / 596553679969) ∧
    -Real.log (250000000000 / 596553679969) ≤ (108713539 / 125000000) := by
  have h := checkLog_sound (w := (96553679969 / 1096553679969)) (n := 12)
    (lo := (17656113 / 100000000)) (hi := (176561131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596553679969 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(596553679969 / 500000000000) = 1/(250000000000 / 596553679969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (86970831 / 100000000) (108713539 / 125000000) (Real.log (596553679969 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (596553679969 / 250000000000) = -Real.log (250000000000 / 596553679969) := by
    rw [show ((596553679969 / 250000000000) : ℝ) = ((250000000000 / 596553679969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0125

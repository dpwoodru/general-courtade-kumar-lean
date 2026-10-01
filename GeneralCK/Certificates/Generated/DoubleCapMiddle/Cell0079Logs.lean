import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0079
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

theorem reflection_log_1_neg : (350876917 / 1000000000) ≤ -Real.log (640 / 909) ∧
    -Real.log (640 / 909) ≤ (175438459 / 500000000) := by
  have h := checkLog_sound (w := (269 / 1549)) (n := 12)
    (lo := (350876917 / 1000000000)) (hi := (175438459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(909 / 640) = 1/(640 / 909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (350876917 / 1000000000) (175438459 / 500000000) (Real.log (909 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (909 / 640) = -Real.log (640 / 909) := by
    rw [show ((909 / 640) : ℝ) = ((640 / 909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (545266113 / 1000000000) ≤ -Real.log (371 / 640) ∧
    -Real.log (371 / 640) ≤ (272633057 / 500000000) := by
  have h := checkLog_sound (w := (269 / 1011)) (n := 12)
    (lo := (545266113 / 1000000000)) (hi := (272633057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 371) = 1/(371 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-272633057 / 500000000) (-545266113 / 1000000000) (Real.log (371 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (175025747 / 500000000) ≤ -Real.log (2560 / 3633) ∧
    -Real.log (2560 / 3633) ≤ (70010299 / 200000000) := by
  have h := checkLog_sound (w := (1073 / 6193)) (n := 12)
    (lo := (175025747 / 500000000)) (hi := (70010299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3633 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3633 / 2560) = 1/(2560 / 3633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (175025747 / 500000000) (70010299 / 200000000) (Real.log (3633 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3633 / 2560) = -Real.log (2560 / 3633) := by
    rw [show ((3633 / 2560) : ℝ) = ((2560 / 3633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (543246591 / 1000000000) ≤ -Real.log (1487 / 2560) ∧
    -Real.log (1487 / 2560) ≤ (2122057 / 3906250) := by
  have h := checkLog_sound (w := (1073 / 4047)) (n := 12)
    (lo := (543246591 / 1000000000)) (hi := (2122057 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1487) = 1/(1487 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2122057 / 3906250) (-543246591 / 1000000000) (Real.log (1487 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (610105187 / 1000000000) ≤ -Real.log (320 / 589) ∧
    -Real.log (320 / 589) ≤ (152526297 / 250000000) := by
  have h := checkLog_sound (w := (269 / 909)) (n := 12)
    (lo := (610105187 / 1000000000)) (hi := (152526297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589 / 320) = 1/(320 / 589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (610105187 / 1000000000) (152526297 / 250000000) (Real.log (589 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (589 / 320) = -Real.log (320 / 589) := by
    rw [show ((589 / 320) : ℝ) = ((320 / 589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1836495361 / 1000000000) ≤ -Real.log (51 / 320) ∧
    -Real.log (51 / 320) ≤ (459123841 / 250000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 51) = 1/(51 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-459123841 / 250000000) (-1836495361 / 1000000000) (Real.log (51 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (608831031 / 1000000000) ≤ -Real.log (1280 / 2353) ∧
    -Real.log (1280 / 2353) ≤ (76103879 / 125000000) := by
  have h := checkLog_sound (w := (1073 / 3633)) (n := 12)
    (lo := (608831031 / 1000000000)) (hi := (76103879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2353 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2353 / 1280) = 1/(1280 / 2353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (608831031 / 1000000000) (76103879 / 125000000) (Real.log (2353 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2353 / 1280) = -Real.log (1280 / 2353) := by
    rw [show ((2353 / 1280) : ℝ) = ((1280 / 2353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (910948281 / 500000000) ≤ -Real.log (207 / 1280) ∧
    -Real.log (207 / 1280) ≤ (364379313 / 200000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 207) = 1/(207 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-364379313 / 200000000) (-910948281 / 500000000) (Real.log (207 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (240879321 / 500000000) ≤ -Real.log (1000000 / 1618919) ∧
    -Real.log (1000000 / 1618919) ≤ (481758643 / 1000000000) := by
  have h := checkLog_sound (w := (618919 / 2618919)) (n := 12)
    (lo := (240879321 / 500000000)) (hi := (481758643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1618919 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1618919 / 1000000) = 1/(1000000 / 1618919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (240879321 / 500000000) (481758643 / 1000000000) (Real.log (1618919 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1618919 / 1000000) = -Real.log (1000000 / 1618919) := by
    rw [show ((1618919 / 1000000) : ℝ) = ((1000000 / 1618919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (964743327 / 1000000000) ≤ -Real.log (381081 / 1000000) ∧
    -Real.log (381081 / 1000000) ≤ (964743329 / 1000000000) := by
  have h := checkLog_sound (w := (118919 / 881081)) (n := 12)
    (lo := (271596147 / 1000000000)) (hi := (67899037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381081) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 381081) = 1/(381081 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-964743329 / 1000000000) (-964743327 / 1000000000) (Real.log (381081 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (241488307 / 500000000) ≤ -Real.log (250000 / 405223) ∧
    -Real.log (250000 / 405223) ≤ (96595323 / 200000000) := by
  have h := checkLog_sound (w := (155223 / 655223)) (n := 12)
    (lo := (241488307 / 500000000)) (hi := (96595323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405223 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(405223 / 250000) = 1/(250000 / 405223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (241488307 / 500000000) (96595323 / 200000000) (Real.log (405223 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (405223 / 250000) = -Real.log (250000 / 405223) := by
    rw [show ((405223 / 250000) : ℝ) = ((250000 / 405223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (969934153 / 1000000000) ≤ -Real.log (94777 / 250000) ∧
    -Real.log (94777 / 250000) ≤ (193986831 / 200000000) := by
  have h := checkLog_sound (w := (30223 / 219777)) (n := 12)
    (lo := (276786973 / 1000000000)) (hi := (138393487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94777) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 94777) = 1/(94777 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-193986831 / 200000000) (-969934153 / 1000000000) (Real.log (94777 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (79630487 / 200000000) ≤ -Real.log (1000000 / 1489071) ∧
    -Real.log (1000000 / 1489071) ≤ (99538109 / 250000000) := by
  have h := checkLog_sound (w := (489071 / 2489071)) (n := 12)
    (lo := (79630487 / 200000000)) (hi := (99538109 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489071 / 1000000) = 1/(1000000 / 1489071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (79630487 / 200000000) (99538109 / 250000000) (Real.log (1489071 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1489071 / 1000000) = -Real.log (1000000 / 1489071) := by
    rw [show ((1489071 / 1000000) : ℝ) = ((1000000 / 1489071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (671524641 / 1000000000) ≤ -Real.log (510929 / 1000000) ∧
    -Real.log (510929 / 1000000) ≤ (335762321 / 500000000) := by
  have h := checkLog_sound (w := (489071 / 1510929)) (n := 12)
    (lo := (671524641 / 1000000000)) (hi := (335762321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 510929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 510929) = 1/(510929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-335762321 / 500000000) (-671524641 / 1000000000) (Real.log (510929 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (39944167 / 100000000) ≤ -Real.log (62500 / 93187) ∧
    -Real.log (62500 / 93187) ≤ (399441671 / 1000000000) := by
  have h := checkLog_sound (w := (30687 / 155687)) (n := 12)
    (lo := (39944167 / 100000000)) (hi := (399441671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93187 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93187 / 62500) = 1/(62500 / 93187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (39944167 / 100000000) (399441671 / 1000000000) (Real.log (93187 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (93187 / 62500) = -Real.log (62500 / 93187) := by
    rw [show ((93187 / 62500) : ℝ) = ((62500 / 93187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (135058309 / 200000000) ≤ -Real.log (31813 / 62500) ∧
    -Real.log (31813 / 62500) ≤ (337645773 / 500000000) := by
  have h := checkLog_sound (w := (30687 / 94313)) (n := 12)
    (lo := (135058309 / 200000000)) (hi := (337645773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 31813) = 1/(31813 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-337645773 / 500000000) (-135058309 / 200000000) (Real.log (31813 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1446501969 / 1000000000) ≤ -Real.log (500000000000 / 2124114033499) ∧
    -Real.log (500000000000 / 2124114033499) ≤ (361625493 / 250000000) := by
  have h := checkLog_sound (w := (124114033499 / 4124114033499)) (n := 12)
    (lo := (60207609 / 1000000000)) (hi := (6020761 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2124114033499 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2124114033499 / 2000000000000) = 1/(500000000000 / 2124114033499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1446501969 / 1000000000) (361625493 / 250000000) (Real.log (2124114033499 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2124114033499 / 500000000000) = -Real.log (500000000000 / 2124114033499) := by
    rw [show ((2124114033499 / 500000000000) : ℝ) = ((500000000000 / 2124114033499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1452910767 / 1000000000) ≤ -Real.log (50000000000 / 213777076717) ∧
    -Real.log (50000000000 / 213777076717) ≤ (145291077 / 100000000) := by
  have h := checkLog_sound (w := (13777076717 / 413777076717)) (n := 12)
    (lo := (66616407 / 1000000000)) (hi := (8327051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213777076717 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(213777076717 / 200000000000) = 1/(50000000000 / 213777076717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1452910767 / 1000000000) (145291077 / 100000000) (Real.log (213777076717 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (213777076717 / 50000000000) = -Real.log (50000000000 / 213777076717) := by
    rw [show ((213777076717 / 50000000000) : ℝ) = ((50000000000 / 213777076717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (267419269 / 250000000) ≤ -Real.log (500000000000 / 1457219104807) ∧
    -Real.log (500000000000 / 1457219104807) ≤ (534838539 / 500000000) := by
  have h := checkLog_sound (w := (457219104807 / 2457219104807)) (n := 12)
    (lo := (47066237 / 125000000)) (hi := (376529897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457219104807 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1457219104807 / 1000000000000) = 1/(500000000000 / 1457219104807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (267419269 / 250000000) (534838539 / 500000000) (Real.log (1457219104807 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1457219104807 / 500000000000) = -Real.log (500000000000 / 1457219104807) := by
    rw [show ((1457219104807 / 500000000000) : ℝ) = ((500000000000 / 1457219104807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (214946643 / 200000000) ≤ -Real.log (15625000000 / 45768927011) ∧
    -Real.log (15625000000 / 45768927011) ≤ (1074733217 / 1000000000) := by
  have h := checkLog_sound (w := (14518927011 / 77018927011)) (n := 12)
    (lo := (76317207 / 200000000)) (hi := (95396509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45768927011 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(45768927011 / 31250000000) = 1/(15625000000 / 45768927011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (214946643 / 200000000) (1074733217 / 1000000000) (Real.log (45768927011 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (45768927011 / 15625000000) = -Real.log (15625000000 / 45768927011) := by
    rw [show ((45768927011 / 15625000000) : ℝ) = ((15625000000 / 45768927011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0079

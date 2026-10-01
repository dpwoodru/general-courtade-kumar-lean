import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0441
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

theorem reflection_log_1_neg : (38069183 / 200000000) ≤ -Real.log (10240 / 12387) ∧
    -Real.log (10240 / 12387) ≤ (47586479 / 250000000) := by
  have h := checkLog_sound (w := (2147 / 22627)) (n := 12)
    (lo := (38069183 / 200000000)) (hi := (47586479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12387 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12387 / 10240) = 1/(10240 / 12387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (38069183 / 200000000) (47586479 / 250000000) (Real.log (12387 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12387 / 10240) = -Real.log (10240 / 12387) := by
    rw [show ((12387 / 10240) : ℝ) = ((10240 / 12387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (235302129 / 1000000000) ≤ -Real.log (8093 / 10240) ∧
    -Real.log (8093 / 10240) ≤ (23530213 / 100000000) := by
  have h := checkLog_sound (w := (2147 / 18333)) (n := 12)
    (lo := (235302129 / 1000000000)) (hi := (23530213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8093) = 1/(8093 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-23530213 / 100000000) (-235302129 / 1000000000) (Real.log (8093 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (190103697 / 1000000000) ≤ -Real.log (320 / 387) ∧
    -Real.log (320 / 387) ≤ (95051849 / 500000000) := by
  have h := checkLog_sound (w := (67 / 707)) (n := 12)
    (lo := (190103697 / 1000000000)) (hi := (95051849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387 / 320) = 1/(320 / 387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (190103697 / 1000000000) (95051849 / 500000000) (Real.log (387 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (387 / 320) = -Real.log (320 / 387) := by
    rw [show ((387 / 320) : ℝ) = ((320 / 387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (234931507 / 1000000000) ≤ -Real.log (253 / 320) ∧
    -Real.log (253 / 320) ≤ (58732877 / 250000000) := by
  have h := checkLog_sound (w := (67 / 573)) (n := 12)
    (lo := (234931507 / 1000000000)) (hi := (58732877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 253) = 1/(253 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58732877 / 250000000) (-234931507 / 1000000000) (Real.log (253 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (43773639 / 125000000) ≤ -Real.log (5120 / 7267) ∧
    -Real.log (5120 / 7267) ≤ (350189113 / 1000000000) := by
  have h := checkLog_sound (w := (2147 / 12387)) (n := 12)
    (lo := (43773639 / 125000000)) (hi := (350189113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7267 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7267 / 5120) = 1/(5120 / 7267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (43773639 / 125000000) (350189113 / 1000000000) (Real.log (7267 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7267 / 5120) = -Real.log (5120 / 7267) := by
    rw [show ((7267 / 5120) : ℝ) = ((5120 / 7267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (108716579 / 200000000) ≤ -Real.log (2973 / 5120) ∧
    -Real.log (2973 / 5120) ≤ (33973931 / 62500000) := by
  have h := checkLog_sound (w := (2147 / 8093)) (n := 12)
    (lo := (108716579 / 200000000)) (hi := (33973931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2973) = 1/(2973 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-33973931 / 62500000) (-108716579 / 200000000) (Real.log (2973 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (174888101 / 500000000) ≤ -Real.log (160 / 227) ∧
    -Real.log (160 / 227) ≤ (349776203 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 387)) (n := 12)
    (lo := (174888101 / 500000000)) (hi := (349776203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227 / 160) = 1/(160 / 227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (174888101 / 500000000) (349776203 / 1000000000) (Real.log (227 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (227 / 160) = -Real.log (160 / 227) := by
    rw [show ((227 / 160) : ℝ) = ((160 / 227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (271287161 / 500000000) ≤ -Real.log (93 / 160) ∧
    -Real.log (93 / 160) ≤ (542574323 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 93) = 1/(93 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-542574323 / 1000000000) (-271287161 / 500000000) (Real.log (93 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (261162003 / 1000000000) ≤ -Real.log (500000 / 649219) ∧
    -Real.log (500000 / 649219) ≤ (65290501 / 250000000) := by
  have h := checkLog_sound (w := (149219 / 1149219)) (n := 12)
    (lo := (261162003 / 1000000000)) (hi := (65290501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649219 / 500000) = 1/(500000 / 649219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (261162003 / 1000000000) (65290501 / 250000000) (Real.log (649219 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (649219 / 500000) = -Real.log (500000 / 649219) := by
    rw [show ((649219 / 500000) : ℝ) = ((500000 / 649219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (354446001 / 1000000000) ≤ -Real.log (350781 / 500000) ∧
    -Real.log (350781 / 500000) ≤ (177223001 / 500000000) := by
  have h := checkLog_sound (w := (149219 / 850781)) (n := 12)
    (lo := (354446001 / 1000000000)) (hi := (177223001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 350781) = 1/(350781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-177223001 / 500000000) (-354446001 / 1000000000) (Real.log (350781 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (130744633 / 500000000) ≤ -Real.log (1000000 / 1298863) ∧
    -Real.log (1000000 / 1298863) ≤ (261489267 / 1000000000) := by
  have h := checkLog_sound (w := (298863 / 2298863)) (n := 12)
    (lo := (130744633 / 500000000)) (hi := (261489267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1298863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1298863 / 1000000) = 1/(1000000 / 1298863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (130744633 / 500000000) (261489267 / 1000000000) (Real.log (1298863 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1298863 / 1000000) = -Real.log (1000000 / 1298863) := by
    rw [show ((1298863 / 1000000) : ℝ) = ((1000000 / 1298863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (14202079 / 40000000) ≤ -Real.log (701137 / 1000000) ∧
    -Real.log (701137 / 1000000) ≤ (44381497 / 125000000) := by
  have h := checkLog_sound (w := (298863 / 1701137)) (n := 12)
    (lo := (14202079 / 40000000)) (hi := (44381497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 701137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 701137) = 1/(701137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-44381497 / 125000000) (-14202079 / 40000000) (Real.log (701137 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (97932629 / 500000000) ≤ -Real.log (1000000 / 1216363) ∧
    -Real.log (1000000 / 1216363) ≤ (195865259 / 1000000000) := by
  have h := checkLog_sound (w := (216363 / 2216363)) (n := 12)
    (lo := (97932629 / 500000000)) (hi := (195865259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1216363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1216363 / 1000000) = 1/(1000000 / 1216363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (97932629 / 500000000) (195865259 / 1000000000) (Real.log (1216363 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1216363 / 1000000) = -Real.log (1000000 / 1216363) := by
    rw [show ((1216363 / 1000000) : ℝ) = ((1000000 / 1216363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (7619043 / 31250000) ≤ -Real.log (783637 / 1000000) ∧
    -Real.log (783637 / 1000000) ≤ (243809377 / 1000000000) := by
  have h := checkLog_sound (w := (216363 / 1783637)) (n := 12)
    (lo := (7619043 / 31250000)) (hi := (243809377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 783637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 783637) = 1/(783637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-243809377 / 1000000000) (-7619043 / 31250000) (Real.log (783637 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (196132413 / 1000000000) ≤ -Real.log (62500 / 76043) ∧
    -Real.log (62500 / 76043) ≤ (98066207 / 500000000) := by
  have h := checkLog_sound (w := (13543 / 138543)) (n := 12)
    (lo := (196132413 / 1000000000)) (hi := (98066207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76043 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76043 / 62500) = 1/(62500 / 76043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (196132413 / 1000000000) (98066207 / 500000000) (Real.log (76043 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (76043 / 62500) = -Real.log (62500 / 76043) := by
    rw [show ((76043 / 62500) : ℝ) = ((62500 / 76043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (122112097 / 500000000) ≤ -Real.log (48957 / 62500) ∧
    -Real.log (48957 / 62500) ≤ (48844839 / 200000000) := by
  have h := checkLog_sound (w := (13543 / 111457)) (n := 12)
    (lo := (122112097 / 500000000)) (hi := (48844839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48957) = 1/(48957 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-48844839 / 200000000) (-122112097 / 500000000) (Real.log (48957 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (153902001 / 250000000) ≤ -Real.log (500000000000 / 925390770879) ∧
    -Real.log (500000000000 / 925390770879) ≤ (123121601 / 200000000) := by
  have h := checkLog_sound (w := (425390770879 / 1425390770879)) (n := 12)
    (lo := (153902001 / 250000000)) (hi := (123121601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((925390770879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(925390770879 / 500000000000) = 1/(500000000000 / 925390770879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (153902001 / 250000000) (123121601 / 200000000) (Real.log (925390770879 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (925390770879 / 500000000000) = -Real.log (500000000000 / 925390770879) := by
    rw [show ((925390770879 / 500000000000) : ℝ) = ((500000000000 / 925390770879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (308270621 / 500000000) ≤ -Real.log (250000000000 / 463127391651) ∧
    -Real.log (250000000000 / 463127391651) ≤ (616541243 / 1000000000) := by
  have h := checkLog_sound (w := (213127391651 / 713127391651)) (n := 12)
    (lo := (308270621 / 500000000)) (hi := (616541243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463127391651 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463127391651 / 250000000000) = 1/(250000000000 / 463127391651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (308270621 / 500000000) (616541243 / 1000000000) (Real.log (463127391651 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (463127391651 / 250000000000) = -Real.log (250000000000 / 463127391651) := by
    rw [show ((463127391651 / 250000000000) : ℝ) = ((250000000000 / 463127391651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (219837317 / 500000000) ≤ -Real.log (50000000000 / 77610105189) ∧
    -Real.log (50000000000 / 77610105189) ≤ (87934927 / 200000000) := by
  have h := checkLog_sound (w := (27610105189 / 127610105189)) (n := 12)
    (lo := (219837317 / 500000000)) (hi := (87934927 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77610105189 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77610105189 / 50000000000) = 1/(50000000000 / 77610105189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (219837317 / 500000000) (87934927 / 200000000) (Real.log (77610105189 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (77610105189 / 50000000000) = -Real.log (50000000000 / 77610105189) := by
    rw [show ((77610105189 / 50000000000) : ℝ) = ((50000000000 / 77610105189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (440356607 / 1000000000) ≤ -Real.log (500000000000 / 776630512491) ∧
    -Real.log (500000000000 / 776630512491) ≤ (1720143 / 3906250) := by
  have h := checkLog_sound (w := (276630512491 / 1276630512491)) (n := 12)
    (lo := (440356607 / 1000000000)) (hi := (1720143 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776630512491 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776630512491 / 500000000000) = 1/(500000000000 / 776630512491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (440356607 / 1000000000) (1720143 / 3906250) (Real.log (776630512491 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (776630512491 / 500000000000) = -Real.log (500000000000 / 776630512491) := by
    rw [show ((776630512491 / 500000000000) : ℝ) = ((500000000000 / 776630512491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0441

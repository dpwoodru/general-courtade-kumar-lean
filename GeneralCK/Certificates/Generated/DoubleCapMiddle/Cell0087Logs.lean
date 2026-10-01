import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0087
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

theorem reflection_log_1_neg : (344254377 / 1000000000) ≤ -Real.log (640 / 903) ∧
    -Real.log (640 / 903) ≤ (172127189 / 500000000) := by
  have h := checkLog_sound (w := (263 / 1543)) (n := 12)
    (lo := (344254377 / 1000000000)) (hi := (172127189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903 / 640) = 1/(640 / 903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (344254377 / 1000000000) (172127189 / 500000000) (Real.log (903 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (903 / 640) = -Real.log (640 / 903) := by
    rw [show ((903 / 640) : ℝ) = ((640 / 903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (132305747 / 250000000) ≤ -Real.log (377 / 640) ∧
    -Real.log (377 / 640) ≤ (529222989 / 1000000000) := by
  have h := checkLog_sound (w := (263 / 1017)) (n := 12)
    (lo := (132305747 / 250000000)) (hi := (529222989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 377) = 1/(377 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-529222989 / 1000000000) (-132305747 / 250000000) (Real.log (377 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (343423467 / 1000000000) ≤ -Real.log (2560 / 3609) ∧
    -Real.log (2560 / 3609) ≤ (85855867 / 250000000) := by
  have h := checkLog_sound (w := (1049 / 6169)) (n := 12)
    (lo := (343423467 / 1000000000)) (hi := (85855867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3609 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3609 / 2560) = 1/(2560 / 3609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (343423467 / 1000000000) (85855867 / 250000000) (Real.log (3609 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3609 / 2560) = -Real.log (2560 / 3609) := by
    rw [show ((3609 / 2560) : ℝ) = ((2560 / 3609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (21089423 / 40000000) ≤ -Real.log (1511 / 2560) ∧
    -Real.log (1511 / 2560) ≤ (65904447 / 125000000) := by
  have h := checkLog_sound (w := (1049 / 4071)) (n := 12)
    (lo := (21089423 / 40000000)) (hi := (65904447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1511) = 1/(1511 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65904447 / 125000000) (-21089423 / 40000000) (Real.log (1511 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (59986619 / 100000000) ≤ -Real.log (320 / 583) ∧
    -Real.log (320 / 583) ≤ (599866191 / 1000000000) := by
  have h := checkLog_sound (w := (263 / 903)) (n := 12)
    (lo := (59986619 / 100000000)) (hi := (599866191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583 / 320) = 1/(320 / 583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (59986619 / 100000000) (599866191 / 1000000000) (Real.log (583 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (583 / 320) = -Real.log (320 / 583) := by
    rw [show ((583 / 320) : ℝ) = ((320 / 583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (862634863 / 500000000) ≤ -Real.log (57 / 320) ∧
    -Real.log (57 / 320) ≤ (1725269729 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 57) = 1/(57 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1725269729 / 1000000000) (-862634863 / 500000000) (Real.log (57 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18705591 / 31250000) ≤ -Real.log (1280 / 2329) ∧
    -Real.log (1280 / 2329) ≤ (598578913 / 1000000000) := by
  have h := checkLog_sound (w := (1049 / 3609)) (n := 12)
    (lo := (18705591 / 31250000)) (hi := (598578913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2329 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2329 / 1280) = 1/(1280 / 2329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18705591 / 31250000) (598578913 / 1000000000) (Real.log (2329 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2329 / 1280) = -Real.log (1280 / 2329) := by
    rw [show ((2329 / 1280) : ℝ) = ((1280 / 2329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (342439529 / 200000000) ≤ -Real.log (231 / 1280) ∧
    -Real.log (231 / 1280) ≤ (107012353 / 62500000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 231) = 1/(231 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-107012353 / 62500000) (-342439529 / 200000000) (Real.log (231 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (59007221 / 125000000) ≤ -Real.log (100000 / 160329) ∧
    -Real.log (100000 / 160329) ≤ (472057769 / 1000000000) := by
  have h := checkLog_sound (w := (60329 / 260329)) (n := 12)
    (lo := (59007221 / 125000000)) (hi := (472057769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160329 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160329 / 100000) = 1/(100000 / 160329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (59007221 / 125000000) (472057769 / 1000000000) (Real.log (160329 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (160329 / 100000) = -Real.log (100000 / 160329) := by
    rw [show ((160329 / 100000) : ℝ) = ((100000 / 160329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (924549743 / 1000000000) ≤ -Real.log (39671 / 100000) ∧
    -Real.log (39671 / 100000) ≤ (184909949 / 200000000) := by
  have h := checkLog_sound (w := (10329 / 89671)) (n := 12)
    (lo := (231402563 / 1000000000)) (hi := (57850641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39671) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 39671) = 1/(39671 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-184909949 / 200000000) (-924549743 / 1000000000) (Real.log (39671 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (473267671 / 1000000000) ≤ -Real.log (1000000 / 1605231) ∧
    -Real.log (1000000 / 1605231) ≤ (59158459 / 125000000) := by
  have h := checkLog_sound (w := (605231 / 2605231)) (n := 12)
    (lo := (473267671 / 1000000000)) (hi := (59158459 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1605231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1605231 / 1000000) = 1/(1000000 / 1605231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (473267671 / 1000000000) (59158459 / 125000000) (Real.log (1605231 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1605231 / 1000000) = -Real.log (1000000 / 1605231) := by
    rw [show ((1605231 / 1000000) : ℝ) = ((1000000 / 1605231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (464727247 / 500000000) ≤ -Real.log (394769 / 1000000) ∧
    -Real.log (394769 / 1000000) ≤ (29045453 / 31250000) := by
  have h := checkLog_sound (w := (105231 / 894769)) (n := 12)
    (lo := (118153657 / 500000000)) (hi := (47261463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394769) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 394769) = 1/(394769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-29045453 / 31250000) (-464727247 / 500000000) (Real.log (394769 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (387969617 / 1000000000) ≤ -Real.log (200000 / 294797) ∧
    -Real.log (200000 / 294797) ≤ (193984809 / 500000000) := by
  have h := checkLog_sound (w := (94797 / 494797)) (n := 12)
    (lo := (387969617 / 1000000000)) (hi := (193984809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294797 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294797 / 200000) = 1/(200000 / 294797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (387969617 / 1000000000) (193984809 / 500000000) (Real.log (294797 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (294797 / 200000) = -Real.log (200000 / 294797) := by
    rw [show ((294797 / 200000) : ℝ) = ((200000 / 294797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (642425549 / 1000000000) ≤ -Real.log (105203 / 200000) ∧
    -Real.log (105203 / 200000) ≤ (12848511 / 20000000) := by
  have h := checkLog_sound (w := (94797 / 305203)) (n := 12)
    (lo := (642425549 / 1000000000)) (hi := (12848511 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 105203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 105203) = 1/(105203 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-12848511 / 20000000) (-642425549 / 1000000000) (Real.log (105203 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (48653923 / 125000000) ≤ -Real.log (500000 / 737923) ∧
    -Real.log (500000 / 737923) ≤ (77846277 / 200000000) := by
  have h := checkLog_sound (w := (237923 / 1237923)) (n := 12)
    (lo := (48653923 / 125000000)) (hi := (77846277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737923 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737923 / 500000) = 1/(500000 / 737923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (48653923 / 125000000) (77846277 / 200000000) (Real.log (737923 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (737923 / 500000) = -Real.log (500000 / 737923) := by
    rw [show ((737923 / 500000) : ℝ) = ((500000 / 737923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (40373109 / 62500000) ≤ -Real.log (262077 / 500000) ∧
    -Real.log (262077 / 500000) ≤ (129193949 / 200000000) := by
  have h := checkLog_sound (w := (237923 / 762077)) (n := 12)
    (lo := (40373109 / 62500000)) (hi := (129193949 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 262077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 262077) = 1/(262077 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-129193949 / 200000000) (-40373109 / 62500000) (Real.log (262077 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (139660751 / 100000000) ≤ -Real.log (125000000000 / 505183257291) ∧
    -Real.log (125000000000 / 505183257291) ≤ (1396607513 / 1000000000) := by
  have h := checkLog_sound (w := (5183257291 / 1005183257291)) (n := 12)
    (lo := (206263 / 20000000)) (hi := (10313151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((505183257291 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(505183257291 / 500000000000) = 1/(125000000000 / 505183257291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (139660751 / 100000000) (1396607513 / 1000000000) (Real.log (505183257291 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (505183257291 / 125000000000) = -Real.log (125000000000 / 505183257291) := by
    rw [show ((505183257291 / 125000000000) : ℝ) = ((125000000000 / 505183257291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (280544433 / 200000000) ≤ -Real.log (125000000000 / 508281741981) ∧
    -Real.log (125000000000 / 508281741981) ≤ (175340271 / 125000000) := by
  have h := checkLog_sound (w := (8281741981 / 1008281741981)) (n := 12)
    (lo := (3285561 / 200000000)) (hi := (8213903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((508281741981 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(508281741981 / 500000000000) = 1/(125000000000 / 508281741981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (280544433 / 200000000) (175340271 / 125000000) (Real.log (508281741981 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (508281741981 / 125000000000) = -Real.log (125000000000 / 508281741981) := by
    rw [show ((508281741981 / 125000000000) : ℝ) = ((125000000000 / 508281741981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (515197583 / 500000000) ≤ -Real.log (250000000000 / 700543235459) ∧
    -Real.log (250000000000 / 700543235459) ≤ (32199849 / 31250000) := by
  have h := checkLog_sound (w := (200543235459 / 1200543235459)) (n := 12)
    (lo := (168623993 / 500000000)) (hi := (337247987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700543235459 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(700543235459 / 500000000000) = 1/(250000000000 / 700543235459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (515197583 / 500000000) (32199849 / 31250000) (Real.log (700543235459 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (700543235459 / 250000000000) = -Real.log (250000000000 / 700543235459) := by
    rw [show ((700543235459 / 250000000000) : ℝ) = ((250000000000 / 700543235459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (129400141 / 125000000) ≤ -Real.log (2500000000 / 7039181233) ∧
    -Real.log (2500000000 / 7039181233) ≤ (103520113 / 100000000) := by
  have h := checkLog_sound (w := (2039181233 / 12039181233)) (n := 12)
    (lo := (85513487 / 250000000)) (hi := (342053949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7039181233 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(7039181233 / 5000000000) = 1/(2500000000 / 7039181233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (129400141 / 125000000) (103520113 / 100000000) (Real.log (7039181233 / 2500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7039181233 / 2500000000) = -Real.log (2500000000 / 7039181233) := by
    rw [show ((7039181233 / 2500000000) : ℝ) = ((2500000000 / 7039181233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0087

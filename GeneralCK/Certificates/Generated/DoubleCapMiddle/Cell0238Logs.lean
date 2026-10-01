import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0238
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

theorem reflection_log_1_neg : (124222867 / 500000000) ≤ -Real.log (1280 / 1641) ∧
    -Real.log (1280 / 1641) ≤ (49689147 / 200000000) := by
  have h := checkLog_sound (w := (361 / 2921)) (n := 12)
    (lo := (124222867 / 500000000)) (hi := (49689147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1641 / 1280) = 1/(1280 / 1641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (124222867 / 500000000) (49689147 / 200000000) (Real.log (1641 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1641 / 1280) = -Real.log (1280 / 1641) := by
    rw [show ((1641 / 1280) : ℝ) = ((1280 / 1641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (165664617 / 500000000) ≤ -Real.log (919 / 1280) ∧
    -Real.log (919 / 1280) ≤ (66265847 / 200000000) := by
  have h := checkLog_sound (w := (361 / 2199)) (n := 12)
    (lo := (165664617 / 500000000)) (hi := (66265847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 919) = 1/(919 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-66265847 / 200000000) (-165664617 / 500000000) (Real.log (919 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (247988591 / 1000000000) ≤ -Real.log (5120 / 6561) ∧
    -Real.log (5120 / 6561) ≤ (15499287 / 62500000) := by
  have h := checkLog_sound (w := (1441 / 11681)) (n := 12)
    (lo := (247988591 / 1000000000)) (hi := (15499287 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6561 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6561 / 5120) = 1/(5120 / 6561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (247988591 / 1000000000) (15499287 / 62500000) (Real.log (6561 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6561 / 5120) = -Real.log (5120 / 6561) := by
    rw [show ((6561 / 5120) : ℝ) = ((5120 / 6561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (165256731 / 500000000) ≤ -Real.log (3679 / 5120) ∧
    -Real.log (3679 / 5120) ≤ (330513463 / 1000000000) := by
  have h := checkLog_sound (w := (1441 / 8799)) (n := 12)
    (lo := (165256731 / 500000000)) (hi := (330513463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3679) = 1/(3679 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-330513463 / 1000000000) (-165256731 / 500000000) (Real.log (3679 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (223643301 / 500000000) ≤ -Real.log (640 / 1001) ∧
    -Real.log (640 / 1001) ≤ (447286603 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 1641)) (n := 12)
    (lo := (223643301 / 500000000)) (hi := (447286603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1001 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1001 / 640) = 1/(640 / 1001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (223643301 / 500000000) (447286603 / 1000000000) (Real.log (1001 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1001 / 640) = -Real.log (640 / 1001) := by
    rw [show ((1001 / 640) : ℝ) = ((640 / 1001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (830256393 / 1000000000) ≤ -Real.log (279 / 640) ∧
    -Real.log (279 / 640) ≤ (166051279 / 200000000) := by
  have h := checkLog_sound (w := (41 / 599)) (n := 12)
    (lo := (137109213 / 1000000000)) (hi := (68554607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 279) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 279) = 1/(279 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-166051279 / 200000000) (-830256393 / 1000000000) (Real.log (279 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (446537071 / 1000000000) ≤ -Real.log (2560 / 4001) ∧
    -Real.log (2560 / 4001) ≤ (27908567 / 62500000) := by
  have h := checkLog_sound (w := (1441 / 6561)) (n := 12)
    (lo := (446537071 / 1000000000)) (hi := (27908567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4001 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4001 / 2560) = 1/(2560 / 4001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (446537071 / 1000000000) (27908567 / 62500000) (Real.log (4001 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4001 / 2560) = -Real.log (2560 / 4001) := by
    rw [show ((4001 / 2560) : ℝ) = ((2560 / 4001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (206892957 / 250000000) ≤ -Real.log (1119 / 2560) ∧
    -Real.log (1119 / 2560) ≤ (82757183 / 100000000) := by
  have h := checkLog_sound (w := (161 / 2399)) (n := 12)
    (lo := (16803081 / 125000000)) (hi := (134424649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1119) = 1/(1119 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-82757183 / 100000000) (-206892957 / 250000000) (Real.log (1119 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67881727 / 200000000) ≤ -Real.log (1000000 / 1404117) ∧
    -Real.log (1000000 / 1404117) ≤ (84852159 / 250000000) := by
  have h := checkLog_sound (w := (404117 / 2404117)) (n := 12)
    (lo := (67881727 / 200000000)) (hi := (84852159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1404117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1404117 / 1000000) = 1/(1000000 / 1404117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67881727 / 200000000) (84852159 / 250000000) (Real.log (1404117 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1404117 / 1000000) = -Real.log (1000000 / 1404117) := by
    rw [show ((1404117 / 1000000) : ℝ) = ((1000000 / 1404117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (517710939 / 1000000000) ≤ -Real.log (595883 / 1000000) ∧
    -Real.log (595883 / 1000000) ≤ (25885547 / 50000000) := by
  have h := checkLog_sound (w := (404117 / 1595883)) (n := 12)
    (lo := (517710939 / 1000000000)) (hi := (25885547 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 595883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 595883) = 1/(595883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-25885547 / 50000000) (-517710939 / 1000000000) (Real.log (595883 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (340029473 / 1000000000) ≤ -Real.log (1000000 / 1404989) ∧
    -Real.log (1000000 / 1404989) ≤ (170014737 / 500000000) := by
  have h := checkLog_sound (w := (404989 / 2404989)) (n := 12)
    (lo := (340029473 / 1000000000)) (hi := (170014737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1404989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1404989 / 1000000) = 1/(1000000 / 1404989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (340029473 / 1000000000) (170014737 / 500000000) (Real.log (1404989 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1404989 / 1000000) = -Real.log (1000000 / 1404989) := by
    rw [show ((1404989 / 1000000) : ℝ) = ((1000000 / 1404989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (259587693 / 500000000) ≤ -Real.log (595011 / 1000000) ∧
    -Real.log (595011 / 1000000) ≤ (519175387 / 1000000000) := by
  have h := checkLog_sound (w := (404989 / 1595011)) (n := 12)
    (lo := (259587693 / 500000000)) (hi := (519175387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 595011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 595011) = 1/(595011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-519175387 / 1000000000) (-259587693 / 500000000) (Real.log (595011 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (5235959 / 20000000) ≤ -Real.log (15625 / 20301) ∧
    -Real.log (15625 / 20301) ≤ (261797951 / 1000000000) := by
  have h := checkLog_sound (w := (2338 / 17963)) (n := 12)
    (lo := (5235959 / 20000000)) (hi := (261797951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20301 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20301 / 15625) = 1/(15625 / 20301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (5235959 / 20000000) (261797951 / 1000000000) (Real.log (20301 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (20301 / 15625) = -Real.log (15625 / 20301) := by
    rw [show ((20301 / 15625) : ℝ) = ((15625 / 20301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (355624067 / 1000000000) ≤ -Real.log (10949 / 15625) ∧
    -Real.log (10949 / 15625) ≤ (88906017 / 250000000) := by
  have h := checkLog_sound (w := (2338 / 13287)) (n := 12)
    (lo := (355624067 / 1000000000)) (hi := (88906017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10949) = 1/(10949 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-88906017 / 250000000) (-355624067 / 1000000000) (Real.log (10949 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (65585489 / 250000000) ≤ -Real.log (1000000 / 1299971) ∧
    -Real.log (1000000 / 1299971) ≤ (262341957 / 1000000000) := by
  have h := checkLog_sound (w := (299971 / 2299971)) (n := 12)
    (lo := (65585489 / 250000000)) (hi := (262341957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299971 / 1000000) = 1/(1000000 / 1299971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (65585489 / 250000000) (262341957 / 1000000000) (Real.log (1299971 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1299971 / 1000000) = -Real.log (1000000 / 1299971) := by
    rw [show ((1299971 / 1000000) : ℝ) = ((1000000 / 1299971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (89158379 / 250000000) ≤ -Real.log (700029 / 1000000) ∧
    -Real.log (700029 / 1000000) ≤ (356633517 / 1000000000) := by
  have h := checkLog_sound (w := (299971 / 1700029)) (n := 12)
    (lo := (89158379 / 250000000)) (hi := (356633517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 700029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 700029) = 1/(700029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-356633517 / 1000000000) (-89158379 / 250000000) (Real.log (700029 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (428559787 / 500000000) ≤ -Real.log (97656250 / 230113631) ∧
    -Real.log (97656250 / 230113631) ≤ (107139947 / 125000000) := by
  have h := checkLog_sound (w := (34801131 / 425426131)) (n := 12)
    (lo := (81986197 / 500000000)) (hi := (32794479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230113631 / 195312500) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(230113631 / 195312500) = 1/(97656250 / 230113631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (428559787 / 500000000) (107139947 / 125000000) (Real.log (230113631 / 97656250)) := by
  have h := reflection_log_17_neg
  have he : Real.log (230113631 / 97656250) = -Real.log (97656250 / 230113631) := by
    rw [show ((230113631 / 97656250) : ℝ) = ((97656250 / 230113631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (859204859 / 1000000000) ≤ -Real.log (50000000000 / 118064119823) ∧
    -Real.log (50000000000 / 118064119823) ≤ (859204861 / 1000000000) := by
  have h := checkLog_sound (w := (18064119823 / 218064119823)) (n := 12)
    (lo := (166057679 / 1000000000)) (hi := (2075721 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118064119823 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(118064119823 / 100000000000) = 1/(50000000000 / 118064119823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (859204859 / 1000000000) (859204861 / 1000000000) (Real.log (118064119823 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (118064119823 / 50000000000) = -Real.log (50000000000 / 118064119823) := by
    rw [show ((118064119823 / 50000000000) : ℝ) = ((50000000000 / 118064119823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (308711009 / 500000000) ≤ -Real.log (62500000000 / 115883870673) ∧
    -Real.log (62500000000 / 115883870673) ≤ (617422019 / 1000000000) := by
  have h := checkLog_sound (w := (53383870673 / 178383870673)) (n := 12)
    (lo := (308711009 / 500000000)) (hi := (617422019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115883870673 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115883870673 / 62500000000) = 1/(62500000000 / 115883870673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (308711009 / 500000000) (617422019 / 1000000000) (Real.log (115883870673 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (115883870673 / 62500000000) = -Real.log (62500000000 / 115883870673) := by
    rw [show ((115883870673 / 62500000000) : ℝ) = ((62500000000 / 115883870673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (38685967 / 62500000) ≤ -Real.log (10000000000 / 18570244947) ∧
    -Real.log (10000000000 / 18570244947) ≤ (618975473 / 1000000000) := by
  have h := checkLog_sound (w := (8570244947 / 28570244947)) (n := 12)
    (lo := (38685967 / 62500000)) (hi := (618975473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18570244947 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18570244947 / 10000000000) = 1/(10000000000 / 18570244947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (38685967 / 62500000) (618975473 / 1000000000) (Real.log (18570244947 / 10000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (18570244947 / 10000000000) = -Real.log (10000000000 / 18570244947) := by
    rw [show ((18570244947 / 10000000000) : ℝ) = ((10000000000 / 18570244947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0238

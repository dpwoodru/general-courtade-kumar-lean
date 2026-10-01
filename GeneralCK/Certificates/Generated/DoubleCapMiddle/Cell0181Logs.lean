import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0181
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

theorem reflection_log_1_neg : (27416337 / 100000000) ≤ -Real.log (1024 / 1347) ∧
    -Real.log (1024 / 1347) ≤ (274163371 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 2371)) (n := 12)
    (lo := (27416337 / 100000000)) (hi := (274163371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1347 / 1024) = 1/(1024 / 1347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27416337 / 100000000) (274163371 / 1000000000) (Real.log (1347 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1347 / 1024) = -Real.log (1024 / 1347) := by
    rw [show ((1347 / 1024) : ℝ) = ((1024 / 1347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (189481959 / 500000000) ≤ -Real.log (701 / 1024) ∧
    -Real.log (701 / 1024) ≤ (378963919 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 1725)) (n := 12)
    (lo := (189481959 / 500000000)) (hi := (378963919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 701) = 1/(701 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-378963919 / 1000000000) (-189481959 / 500000000) (Real.log (701 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (273717837 / 1000000000) ≤ -Real.log (1280 / 1683) ∧
    -Real.log (1280 / 1683) ≤ (136858919 / 500000000) := by
  have h := checkLog_sound (w := (403 / 2963)) (n := 12)
    (lo := (273717837 / 1000000000)) (hi := (136858919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1683 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1683 / 1280) = 1/(1280 / 1683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (273717837 / 1000000000) (136858919 / 500000000) (Real.log (1683 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1683 / 1280) = -Real.log (1280 / 1683) := by
    rw [show ((1683 / 1280) : ℝ) = ((1280 / 1683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (94527091 / 250000000) ≤ -Real.log (877 / 1280) ∧
    -Real.log (877 / 1280) ≤ (75621673 / 200000000) := by
  have h := checkLog_sound (w := (403 / 2157)) (n := 12)
    (lo := (94527091 / 250000000)) (hi := (75621673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 877) = 1/(877 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-75621673 / 200000000) (-94527091 / 250000000) (Real.log (877 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (489107099 / 1000000000) ≤ -Real.log (512 / 835) ∧
    -Real.log (512 / 835) ≤ (4891071 / 10000000) := by
  have h := checkLog_sound (w := (323 / 1347)) (n := 12)
    (lo := (489107099 / 1000000000)) (hi := (4891071 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835 / 512) = 1/(512 / 835) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (489107099 / 1000000000) (4891071 / 10000000) (Real.log (835 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (835 / 512) = -Real.log (512 / 835) := by
    rw [show ((835 / 512) : ℝ) = ((512 / 835) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (996577609 / 1000000000) ≤ -Real.log (189 / 512) ∧
    -Real.log (189 / 512) ≤ (996577611 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 445)) (n := 12)
    (lo := (303430429 / 1000000000)) (hi := (30343043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 189) = 1/(189 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-996577611 / 1000000000) (-996577609 / 1000000000) (Real.log (189 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (244194139 / 500000000) ≤ -Real.log (640 / 1043) ∧
    -Real.log (640 / 1043) ≤ (488388279 / 1000000000) := by
  have h := checkLog_sound (w := (403 / 1683)) (n := 12)
    (lo := (244194139 / 500000000)) (hi := (488388279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1043 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1043 / 640) = 1/(640 / 1043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (244194139 / 500000000) (488388279 / 1000000000) (Real.log (1043 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1043 / 640) = -Real.log (640 / 1043) := by
    rw [show ((1043 / 640) : ℝ) = ((640 / 1043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (496704017 / 500000000) ≤ -Real.log (237 / 640) ∧
    -Real.log (237 / 640) ≤ (248352009 / 250000000) := by
  have h := checkLog_sound (w := (83 / 557)) (n := 12)
    (lo := (150130427 / 500000000)) (hi := (60052171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 237) = 1/(237 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-248352009 / 250000000) (-496704017 / 500000000) (Real.log (237 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (187218677 / 500000000) ≤ -Real.log (1000000 / 1454173) ∧
    -Real.log (1000000 / 1454173) ≤ (74887471 / 200000000) := by
  have h := checkLog_sound (w := (454173 / 2454173)) (n := 12)
    (lo := (187218677 / 500000000)) (hi := (74887471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1454173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1454173 / 1000000) = 1/(1000000 / 1454173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (187218677 / 500000000) (74887471 / 200000000) (Real.log (1454173 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1454173 / 1000000) = -Real.log (1000000 / 1454173) := by
    rw [show ((1454173 / 1000000) : ℝ) = ((1000000 / 1454173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (605453203 / 1000000000) ≤ -Real.log (545827 / 1000000) ∧
    -Real.log (545827 / 1000000) ≤ (151363301 / 250000000) := by
  have h := checkLog_sound (w := (454173 / 1545827)) (n := 12)
    (lo := (605453203 / 1000000000)) (hi := (151363301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 545827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 545827) = 1/(545827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-151363301 / 250000000) (-605453203 / 1000000000) (Real.log (545827 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (11720223 / 31250000) ≤ -Real.log (50000 / 72753) ∧
    -Real.log (50000 / 72753) ≤ (375047137 / 1000000000) := by
  have h := checkLog_sound (w := (22753 / 122753)) (n := 12)
    (lo := (11720223 / 31250000)) (hi := (375047137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72753 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72753 / 50000) = 1/(50000 / 72753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (11720223 / 31250000) (375047137 / 1000000000) (Real.log (72753 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (72753 / 50000) = -Real.log (50000 / 72753) := by
    rw [show ((72753 / 50000) : ℝ) = ((50000 / 72753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (303539791 / 500000000) ≤ -Real.log (27247 / 50000) ∧
    -Real.log (27247 / 50000) ≤ (607079583 / 1000000000) := by
  have h := checkLog_sound (w := (22753 / 77247)) (n := 12)
    (lo := (303539791 / 500000000)) (hi := (607079583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 27247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 27247) = 1/(27247 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-607079583 / 1000000000) (-303539791 / 500000000) (Real.log (27247 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (293076993 / 1000000000) ≤ -Real.log (500000 / 670273) ∧
    -Real.log (500000 / 670273) ≤ (146538497 / 500000000) := by
  have h := checkLog_sound (w := (170273 / 1170273)) (n := 12)
    (lo := (293076993 / 1000000000)) (hi := (146538497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670273 / 500000) = 1/(500000 / 670273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (293076993 / 1000000000) (146538497 / 500000000) (Real.log (670273 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (670273 / 500000) = -Real.log (500000 / 670273) := by
    rw [show ((670273 / 500000) : ℝ) = ((500000 / 670273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (416343059 / 1000000000) ≤ -Real.log (329727 / 500000) ∧
    -Real.log (329727 / 500000) ≤ (20817153 / 50000000) := by
  have h := checkLog_sound (w := (170273 / 829727)) (n := 12)
    (lo := (416343059 / 1000000000)) (hi := (20817153 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 329727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 329727) = 1/(329727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-20817153 / 50000000) (-416343059 / 1000000000) (Real.log (329727 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (18352083 / 62500000) ≤ -Real.log (250000 / 335323) ∧
    -Real.log (250000 / 335323) ≤ (293633329 / 1000000000) := by
  have h := checkLog_sound (w := (85323 / 585323)) (n := 12)
    (lo := (18352083 / 62500000)) (hi := (293633329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335323 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335323 / 250000) = 1/(250000 / 335323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (18352083 / 62500000) (293633329 / 1000000000) (Real.log (335323 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (335323 / 250000) = -Real.log (250000 / 335323) := by
    rw [show ((335323 / 250000) : ℝ) = ((250000 / 335323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (208737469 / 500000000) ≤ -Real.log (164677 / 250000) ∧
    -Real.log (164677 / 250000) ≤ (417474939 / 1000000000) := by
  have h := checkLog_sound (w := (85323 / 414677)) (n := 12)
    (lo := (208737469 / 500000000)) (hi := (417474939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 164677) = 1/(164677 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-417474939 / 1000000000) (-208737469 / 500000000) (Real.log (164677 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (244972639 / 250000000) ≤ -Real.log (500000000000 / 1332082326451) ∧
    -Real.log (500000000000 / 1332082326451) ≤ (489945279 / 500000000) := by
  have h := checkLog_sound (w := (332082326451 / 2332082326451)) (n := 12)
    (lo := (17921461 / 62500000)) (hi := (286743377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1332082326451 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1332082326451 / 1000000000000) = 1/(500000000000 / 1332082326451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (244972639 / 250000000) (489945279 / 500000000) (Real.log (1332082326451 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1332082326451 / 500000000000) = -Real.log (500000000000 / 1332082326451) := by
    rw [show ((1332082326451 / 500000000000) : ℝ) = ((500000000000 / 1332082326451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (491063359 / 500000000) ≤ -Real.log (500000000000 / 1335064410761) ∧
    -Real.log (500000000000 / 1335064410761) ≤ (1534573 / 1562500) := by
  have h := checkLog_sound (w := (335064410761 / 2335064410761)) (n := 12)
    (lo := (144489769 / 500000000)) (hi := (288979539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335064410761 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1335064410761 / 1000000000000) = 1/(500000000000 / 1335064410761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (491063359 / 500000000) (1534573 / 1562500) (Real.log (1335064410761 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1335064410761 / 500000000000) = -Real.log (500000000000 / 1335064410761) := by
    rw [show ((1335064410761 / 500000000000) : ℝ) = ((500000000000 / 1335064410761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (177355013 / 250000000) ≤ -Real.log (20000000000 / 40656239859) ∧
    -Real.log (20000000000 / 40656239859) ≤ (354710027 / 500000000) := by
  have h := checkLog_sound (w := (656239859 / 80656239859)) (n := 12)
    (lo := (2034109 / 125000000)) (hi := (16272873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40656239859 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40656239859 / 40000000000) = 1/(20000000000 / 40656239859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (177355013 / 250000000) (354710027 / 500000000) (Real.log (40656239859 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (40656239859 / 20000000000) = -Real.log (20000000000 / 40656239859) := by
    rw [show ((40656239859 / 20000000000) : ℝ) = ((20000000000 / 40656239859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (355554133 / 500000000) ≤ -Real.log (62500000000 / 127265419579) ∧
    -Real.log (62500000000 / 127265419579) ≤ (177777067 / 250000000) := by
  have h := checkLog_sound (w := (2265419579 / 252265419579)) (n := 12)
    (lo := (8980543 / 500000000)) (hi := (17961087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127265419579 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(127265419579 / 125000000000) = 1/(62500000000 / 127265419579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (355554133 / 500000000) (177777067 / 250000000) (Real.log (127265419579 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (127265419579 / 62500000000) = -Real.log (62500000000 / 127265419579) := by
    rw [show ((127265419579 / 62500000000) : ℝ) = ((62500000000 / 127265419579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0181

import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0381
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

theorem reflection_log_1_neg : (204772711 / 1000000000) ≤ -Real.log (10240 / 12567) ∧
    -Real.log (10240 / 12567) ≤ (25596589 / 125000000) := by
  have h := checkLog_sound (w := (2327 / 22807)) (n := 12)
    (lo := (204772711 / 1000000000)) (hi := (25596589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12567 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12567 / 10240) = 1/(10240 / 12567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (204772711 / 1000000000) (25596589 / 125000000) (Real.log (12567 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12567 / 10240) = -Real.log (10240 / 12567) := by
    rw [show ((12567 / 10240) : ℝ) = ((10240 / 12567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (128897321 / 500000000) ≤ -Real.log (7913 / 10240) ∧
    -Real.log (7913 / 10240) ≤ (257794643 / 1000000000) := by
  have h := checkLog_sound (w := (2327 / 18153)) (n := 12)
    (lo := (128897321 / 500000000)) (hi := (257794643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7913) = 1/(7913 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-257794643 / 1000000000) (-128897321 / 500000000) (Real.log (7913 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (102266981 / 500000000) ≤ -Real.log (2560 / 3141) ∧
    -Real.log (2560 / 3141) ≤ (204533963 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 5701)) (n := 12)
    (lo := (102266981 / 500000000)) (hi := (204533963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3141 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3141 / 2560) = 1/(2560 / 3141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (102266981 / 500000000) (204533963 / 1000000000) (Real.log (3141 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3141 / 2560) = -Real.log (2560 / 3141) := by
    rw [show ((3141 / 2560) : ℝ) = ((2560 / 3141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (257415591 / 1000000000) ≤ -Real.log (1979 / 2560) ∧
    -Real.log (1979 / 2560) ≤ (32176949 / 125000000) := by
  have h := checkLog_sound (w := (581 / 4539)) (n := 12)
    (lo := (257415591 / 1000000000)) (hi := (32176949 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1979) = 1/(1979 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-32176949 / 125000000) (-257415591 / 1000000000) (Real.log (1979 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (374656827 / 1000000000) ≤ -Real.log (5120 / 7447) ∧
    -Real.log (5120 / 7447) ≤ (93664207 / 250000000) := by
  have h := checkLog_sound (w := (2327 / 12567)) (n := 12)
    (lo := (374656827 / 1000000000)) (hi := (93664207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7447 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7447 / 5120) = 1/(5120 / 7447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (374656827 / 1000000000) (93664207 / 250000000) (Real.log (7447 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7447 / 5120) = -Real.log (5120 / 7447) := by
    rw [show ((7447 / 5120) : ℝ) = ((5120 / 7447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (75754769 / 125000000) ≤ -Real.log (2793 / 5120) ∧
    -Real.log (2793 / 5120) ≤ (606038153 / 1000000000) := by
  have h := checkLog_sound (w := (2327 / 7913)) (n := 12)
    (lo := (75754769 / 125000000)) (hi := (606038153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2793) = 1/(2793 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-606038153 / 1000000000) (-75754769 / 125000000) (Real.log (2793 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (374253899 / 1000000000) ≤ -Real.log (1280 / 1861) ∧
    -Real.log (1280 / 1861) ≤ (3742539 / 10000000) := by
  have h := checkLog_sound (w := (581 / 3141)) (n := 12)
    (lo := (374253899 / 1000000000)) (hi := (3742539 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1861 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1861 / 1280) = 1/(1280 / 1861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (374253899 / 1000000000) (3742539 / 10000000) (Real.log (1861 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1861 / 1280) = -Real.log (1280 / 1861) := by
    rw [show ((1861 / 1280) : ℝ) = ((1280 / 1861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (302482307 / 500000000) ≤ -Real.log (699 / 1280) ∧
    -Real.log (699 / 1280) ≤ (120992923 / 200000000) := by
  have h := checkLog_sound (w := (581 / 1979)) (n := 12)
    (lo := (302482307 / 500000000)) (hi := (120992923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 699) = 1/(699 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-120992923 / 200000000) (-302482307 / 500000000) (Real.log (699 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (280642351 / 1000000000) ≤ -Real.log (50000 / 66199) ∧
    -Real.log (50000 / 66199) ≤ (17540147 / 62500000) := by
  have h := checkLog_sound (w := (16199 / 116199)) (n := 12)
    (lo := (280642351 / 1000000000)) (hi := (17540147 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66199 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66199 / 50000) = 1/(50000 / 66199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (280642351 / 1000000000) (17540147 / 62500000) (Real.log (66199 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (66199 / 50000) = -Real.log (50000 / 66199) := by
    rw [show ((66199 / 50000) : ℝ) = ((50000 / 66199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (391532617 / 1000000000) ≤ -Real.log (33801 / 50000) ∧
    -Real.log (33801 / 50000) ≤ (195766309 / 500000000) := by
  have h := checkLog_sound (w := (16199 / 83801)) (n := 12)
    (lo := (391532617 / 1000000000)) (hi := (195766309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33801) = 1/(33801 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-195766309 / 500000000) (-391532617 / 1000000000) (Real.log (33801 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (280965567 / 1000000000) ≤ -Real.log (125000 / 165551) ∧
    -Real.log (125000 / 165551) ≤ (4390087 / 15625000) := by
  have h := checkLog_sound (w := (40551 / 290551)) (n := 12)
    (lo := (280965567 / 1000000000)) (hi := (4390087 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165551 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165551 / 125000) = 1/(125000 / 165551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (280965567 / 1000000000) (4390087 / 15625000) (Real.log (165551 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (165551 / 125000) = -Real.log (125000 / 165551) := by
    rw [show ((165551 / 125000) : ℝ) = ((125000 / 165551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (78433187 / 200000000) ≤ -Real.log (84449 / 125000) ∧
    -Real.log (84449 / 125000) ≤ (24510371 / 62500000) := by
  have h := checkLog_sound (w := (40551 / 209449)) (n := 12)
    (lo := (78433187 / 200000000)) (hi := (24510371 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84449) = 1/(84449 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-24510371 / 62500000) (-78433187 / 200000000) (Real.log (84449 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (211834241 / 1000000000) ≤ -Real.log (1000000 / 1235943) ∧
    -Real.log (1000000 / 1235943) ≤ (105917121 / 500000000) := by
  have h := checkLog_sound (w := (235943 / 2235943)) (n := 12)
    (lo := (211834241 / 1000000000)) (hi := (105917121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235943 / 1000000) = 1/(1000000 / 1235943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (211834241 / 1000000000) (105917121 / 500000000) (Real.log (1235943 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1235943 / 1000000) = -Real.log (1000000 / 1235943) := by
    rw [show ((1235943 / 1000000) : ℝ) = ((1000000 / 1235943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (53822577 / 200000000) ≤ -Real.log (764057 / 1000000) ∧
    -Real.log (764057 / 1000000) ≤ (134556443 / 500000000) := by
  have h := checkLog_sound (w := (235943 / 1764057)) (n := 12)
    (lo := (53822577 / 200000000)) (hi := (134556443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764057) = 1/(764057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-134556443 / 500000000) (-53822577 / 200000000) (Real.log (764057 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (212102017 / 1000000000) ≤ -Real.log (500000 / 618137) ∧
    -Real.log (500000 / 618137) ≤ (106051009 / 500000000) := by
  have h := checkLog_sound (w := (118137 / 1118137)) (n := 12)
    (lo := (212102017 / 1000000000)) (hi := (106051009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618137 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618137 / 500000) = 1/(500000 / 618137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (212102017 / 1000000000) (106051009 / 500000000) (Real.log (618137 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (618137 / 500000) = -Real.log (500000 / 618137) := by
    rw [show ((618137 / 500000) : ℝ) = ((500000 / 618137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16846637 / 62500000) ≤ -Real.log (381863 / 500000) ∧
    -Real.log (381863 / 500000) ≤ (269546193 / 1000000000) := by
  have h := checkLog_sound (w := (118137 / 881863)) (n := 12)
    (lo := (16846637 / 62500000)) (hi := (269546193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381863) = 1/(381863 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-269546193 / 1000000000) (-16846637 / 62500000) (Real.log (381863 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (672174969 / 1000000000) ≤ -Real.log (125000000000 / 244811544037) ∧
    -Real.log (125000000000 / 244811544037) ≤ (67217497 / 100000000) := by
  have h := checkLog_sound (w := (119811544037 / 369811544037)) (n := 12)
    (lo := (672174969 / 1000000000)) (hi := (67217497 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244811544037 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244811544037 / 125000000000) = 1/(125000000000 / 244811544037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (672174969 / 1000000000) (67217497 / 100000000) (Real.log (244811544037 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (244811544037 / 125000000000) = -Real.log (125000000000 / 244811544037) := by
    rw [show ((244811544037 / 125000000000) : ℝ) = ((125000000000 / 244811544037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (336565751 / 500000000) ≤ -Real.log (500000000000 / 980183305901) ∧
    -Real.log (500000000000 / 980183305901) ≤ (673131503 / 1000000000) := by
  have h := checkLog_sound (w := (480183305901 / 1480183305901)) (n := 12)
    (lo := (336565751 / 500000000)) (hi := (673131503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980183305901 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980183305901 / 500000000000) = 1/(500000000000 / 980183305901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (336565751 / 500000000) (673131503 / 1000000000) (Real.log (980183305901 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (980183305901 / 500000000000) = -Real.log (500000000000 / 980183305901) := by
    rw [show ((980183305901 / 500000000000) : ℝ) = ((500000000000 / 980183305901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (240473563 / 500000000) ≤ -Real.log (62500000000 / 101100359659) ∧
    -Real.log (62500000000 / 101100359659) ≤ (480947127 / 1000000000) := by
  have h := checkLog_sound (w := (38600359659 / 163600359659)) (n := 12)
    (lo := (240473563 / 500000000)) (hi := (480947127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101100359659 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101100359659 / 62500000000) = 1/(62500000000 / 101100359659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (240473563 / 500000000) (480947127 / 1000000000) (Real.log (101100359659 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (101100359659 / 62500000000) = -Real.log (62500000000 / 101100359659) := by
    rw [show ((101100359659 / 62500000000) : ℝ) = ((62500000000 / 101100359659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (48164821 / 100000000) ≤ -Real.log (500000000000 / 809370114413) ∧
    -Real.log (500000000000 / 809370114413) ≤ (481648211 / 1000000000) := by
  have h := checkLog_sound (w := (309370114413 / 1309370114413)) (n := 12)
    (lo := (48164821 / 100000000)) (hi := (481648211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809370114413 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(809370114413 / 500000000000) = 1/(500000000000 / 809370114413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (48164821 / 100000000) (481648211 / 1000000000) (Real.log (809370114413 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (809370114413 / 500000000000) = -Real.log (500000000000 / 809370114413) := by
    rw [show ((809370114413 / 500000000000) : ℝ) = ((500000000000 / 809370114413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0381

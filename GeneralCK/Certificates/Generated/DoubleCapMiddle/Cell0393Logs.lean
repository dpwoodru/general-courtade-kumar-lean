import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0393
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

theorem reflection_log_1_neg : (100951977 / 500000000) ≤ -Real.log (10240 / 12531) ∧
    -Real.log (10240 / 12531) ≤ (40380791 / 200000000) := by
  have h := checkLog_sound (w := (2291 / 22771)) (n := 12)
    (lo := (100951977 / 500000000)) (hi := (40380791 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12531 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12531 / 10240) = 1/(10240 / 12531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (100951977 / 500000000) (40380791 / 200000000) (Real.log (12531 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12531 / 10240) = -Real.log (10240 / 12531) := by
    rw [show ((12531 / 10240) : ℝ) = ((10240 / 12531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (50651097 / 200000000) ≤ -Real.log (7949 / 10240) ∧
    -Real.log (7949 / 10240) ≤ (126627743 / 500000000) := by
  have h := checkLog_sound (w := (2291 / 18189)) (n := 12)
    (lo := (50651097 / 200000000)) (hi := (126627743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7949) = 1/(7949 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-126627743 / 500000000) (-50651097 / 200000000) (Real.log (7949 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (201664519 / 1000000000) ≤ -Real.log (640 / 783) ∧
    -Real.log (640 / 783) ≤ (5041613 / 25000000) := by
  have h := checkLog_sound (w := (143 / 1423)) (n := 12)
    (lo := (201664519 / 1000000000)) (hi := (5041613 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783 / 640) = 1/(640 / 783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (201664519 / 1000000000) (5041613 / 25000000) (Real.log (783 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (783 / 640) = -Real.log (640 / 783) := by
    rw [show ((783 / 640) : ℝ) = ((640 / 783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (5057563 / 20000000) ≤ -Real.log (497 / 640) ∧
    -Real.log (497 / 640) ≤ (252878151 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 1137)) (n := 12)
    (lo := (5057563 / 20000000)) (hi := (252878151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 497) = 1/(497 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-252878151 / 1000000000) (-5057563 / 20000000) (Real.log (497 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (369810943 / 1000000000) ≤ -Real.log (5120 / 7411) ∧
    -Real.log (5120 / 7411) ≤ (722287 / 1953125) := by
  have h := checkLog_sound (w := (2291 / 12531)) (n := 12)
    (lo := (369810943 / 1000000000)) (hi := (722287 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7411 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7411 / 5120) = 1/(5120 / 7411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (369810943 / 1000000000) (722287 / 1953125) (Real.log (7411 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7411 / 5120) = -Real.log (5120 / 7411) := by
    rw [show ((7411 / 5120) : ℝ) = ((5120 / 7411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (296615573 / 500000000) ≤ -Real.log (2829 / 5120) ∧
    -Real.log (2829 / 5120) ≤ (593231147 / 1000000000) := by
  have h := checkLog_sound (w := (2291 / 7949)) (n := 12)
    (lo := (296615573 / 500000000)) (hi := (593231147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2829) = 1/(2829 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-593231147 / 1000000000) (-296615573 / 500000000) (Real.log (2829 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (184703029 / 500000000) ≤ -Real.log (320 / 463) ∧
    -Real.log (320 / 463) ≤ (369406059 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 783)) (n := 12)
    (lo := (184703029 / 500000000)) (hi := (369406059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463 / 320) = 1/(320 / 463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (184703029 / 500000000) (369406059 / 1000000000) (Real.log (463 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (463 / 320) = -Real.log (320 / 463) := by
    rw [show ((463 / 320) : ℝ) = ((320 / 463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (592171263 / 1000000000) ≤ -Real.log (177 / 320) ∧
    -Real.log (177 / 320) ≤ (2313169 / 3906250) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 177) = 1/(177 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2313169 / 3906250) (-592171263 / 1000000000) (Real.log (177 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (55353697 / 200000000) ≤ -Real.log (1000000 / 1318861) ∧
    -Real.log (1000000 / 1318861) ≤ (138384243 / 500000000) := by
  have h := checkLog_sound (w := (318861 / 2318861)) (n := 12)
    (lo := (55353697 / 200000000)) (hi := (138384243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1318861 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1318861 / 1000000) = 1/(1000000 / 1318861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (55353697 / 200000000) (138384243 / 500000000) (Real.log (1318861 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1318861 / 1000000) = -Real.log (1000000 / 1318861) := by
    rw [show ((1318861 / 1000000) : ℝ) = ((1000000 / 1318861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (191994441 / 500000000) ≤ -Real.log (681139 / 1000000) ∧
    -Real.log (681139 / 1000000) ≤ (383988883 / 1000000000) := by
  have h := checkLog_sound (w := (318861 / 1681139)) (n := 12)
    (lo := (191994441 / 500000000)) (hi := (383988883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 681139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 681139) = 1/(681139 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-383988883 / 1000000000) (-191994441 / 500000000) (Real.log (681139 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (55418591 / 200000000) ≤ -Real.log (1000000 / 1319289) ∧
    -Real.log (1000000 / 1319289) ≤ (69273239 / 250000000) := by
  have h := checkLog_sound (w := (319289 / 2319289)) (n := 12)
    (lo := (55418591 / 200000000)) (hi := (69273239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319289 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319289 / 1000000) = 1/(1000000 / 1319289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (55418591 / 200000000) (69273239 / 250000000) (Real.log (1319289 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1319289 / 1000000) = -Real.log (1000000 / 1319289) := by
    rw [show ((1319289 / 1000000) : ℝ) = ((1000000 / 1319289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (192308719 / 500000000) ≤ -Real.log (680711 / 1000000) ∧
    -Real.log (680711 / 1000000) ≤ (384617439 / 1000000000) := by
  have h := checkLog_sound (w := (319289 / 1680711)) (n := 12)
    (lo := (192308719 / 500000000)) (hi := (384617439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 680711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 680711) = 1/(680711 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-384617439 / 1000000000) (-192308719 / 500000000) (Real.log (680711 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (208637241 / 1000000000) ≤ -Real.log (500000 / 615999) ∧
    -Real.log (500000 / 615999) ≤ (104318621 / 500000000) := by
  have h := checkLog_sound (w := (115999 / 1115999)) (n := 12)
    (lo := (208637241 / 1000000000)) (hi := (104318621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615999 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615999 / 500000) = 1/(500000 / 615999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (208637241 / 1000000000) (104318621 / 500000000) (Real.log (615999 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (615999 / 500000) = -Real.log (500000 / 615999) := by
    rw [show ((615999 / 500000) : ℝ) = ((500000 / 615999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (263962941 / 1000000000) ≤ -Real.log (384001 / 500000) ∧
    -Real.log (384001 / 500000) ≤ (131981471 / 500000000) := by
  have h := checkLog_sound (w := (115999 / 884001)) (n := 12)
    (lo := (263962941 / 1000000000)) (hi := (131981471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 384001) = 1/(384001 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-131981471 / 500000000) (-263962941 / 1000000000) (Real.log (384001 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (208904251 / 1000000000) ≤ -Real.log (1000000 / 1232327) ∧
    -Real.log (1000000 / 1232327) ≤ (52226063 / 250000000) := by
  have h := checkLog_sound (w := (232327 / 2232327)) (n := 12)
    (lo := (208904251 / 1000000000)) (hi := (52226063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1232327 / 1000000) = 1/(1000000 / 1232327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (208904251 / 1000000000) (52226063 / 250000000) (Real.log (1232327 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1232327 / 1000000) = -Real.log (1000000 / 1232327) := by
    rw [show ((1232327 / 1000000) : ℝ) = ((1000000 / 1232327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (264391417 / 1000000000) ≤ -Real.log (767673 / 1000000) ∧
    -Real.log (767673 / 1000000) ≤ (132195709 / 500000000) := by
  have h := checkLog_sound (w := (232327 / 1767673)) (n := 12)
    (lo := (264391417 / 1000000000)) (hi := (132195709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 767673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 767673) = 1/(767673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-132195709 / 500000000) (-264391417 / 1000000000) (Real.log (767673 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (660757367 / 1000000000) ≤ -Real.log (500000000000 / 968129119019) ∧
    -Real.log (500000000000 / 968129119019) ≤ (82594671 / 125000000) := by
  have h := checkLog_sound (w := (468129119019 / 1468129119019)) (n := 12)
    (lo := (660757367 / 1000000000)) (hi := (82594671 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((968129119019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(968129119019 / 500000000000) = 1/(500000000000 / 968129119019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (660757367 / 1000000000) (82594671 / 125000000) (Real.log (968129119019 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (968129119019 / 500000000000) = -Real.log (500000000000 / 968129119019) := by
    rw [show ((968129119019 / 500000000000) : ℝ) = ((500000000000 / 968129119019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (661710393 / 1000000000) ≤ -Real.log (100000000000 / 193810442317) ∧
    -Real.log (100000000000 / 193810442317) ≤ (330855197 / 500000000) := by
  have h := checkLog_sound (w := (93810442317 / 293810442317)) (n := 12)
    (lo := (661710393 / 1000000000)) (hi := (330855197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193810442317 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193810442317 / 100000000000) = 1/(100000000000 / 193810442317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (661710393 / 1000000000) (330855197 / 500000000) (Real.log (193810442317 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (193810442317 / 100000000000) = -Real.log (100000000000 / 193810442317) := by
    rw [show ((193810442317 / 100000000000) : ℝ) = ((100000000000 / 193810442317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (472600183 / 1000000000) ≤ -Real.log (200000000 / 320831977) ∧
    -Real.log (200000000 / 320831977) ≤ (59075023 / 125000000) := by
  have h := checkLog_sound (w := (120831977 / 520831977)) (n := 12)
    (lo := (472600183 / 1000000000)) (hi := (59075023 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320831977 / 200000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320831977 / 200000000) = 1/(200000000 / 320831977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (472600183 / 1000000000) (59075023 / 125000000) (Real.log (320831977 / 200000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (320831977 / 200000000) = -Real.log (200000000 / 320831977) := by
    rw [show ((320831977 / 200000000) : ℝ) = ((200000000 / 320831977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (473295669 / 1000000000) ≤ -Real.log (250000000000 / 401318986079) ∧
    -Real.log (250000000000 / 401318986079) ≤ (47329567 / 100000000) := by
  have h := checkLog_sound (w := (151318986079 / 651318986079)) (n := 12)
    (lo := (473295669 / 1000000000)) (hi := (47329567 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401318986079 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401318986079 / 250000000000) = 1/(250000000000 / 401318986079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (473295669 / 1000000000) (47329567 / 100000000) (Real.log (401318986079 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (401318986079 / 250000000000) = -Real.log (250000000000 / 401318986079) := by
    rw [show ((401318986079 / 250000000000) : ℝ) = ((250000000000 / 401318986079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0393

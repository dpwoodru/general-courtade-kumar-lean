import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0075
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

theorem reflection_log_1_neg : (354171813 / 1000000000) ≤ -Real.log (40 / 57) ∧
    -Real.log (40 / 57) ≤ (177085907 / 500000000) := by
  have h := checkLog_sound (w := (17 / 97)) (n := 12)
    (lo := (354171813 / 1000000000)) (hi := (177085907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57 / 40) = 1/(40 / 57) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (354171813 / 1000000000) (177085907 / 500000000) (Real.log (57 / 40)) := by
  have h := reflection_log_1_neg
  have he : Real.log (57 / 40) = -Real.log (40 / 57) := by
    rw [show ((57 / 40) : ℝ) = ((40 / 57) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (276692619 / 500000000) ≤ -Real.log (23 / 40) ∧
    -Real.log (23 / 40) ≤ (553385239 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 63)) (n := 12)
    (lo := (276692619 / 500000000)) (hi := (553385239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 23) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 23) = 1/(23 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-553385239 / 1000000000) (-276692619 / 500000000) (Real.log (23 / 40)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (176674553 / 500000000) ≤ -Real.log (512 / 729) ∧
    -Real.log (512 / 729) ≤ (353349107 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1241)) (n := 12)
    (lo := (176674553 / 500000000)) (hi := (353349107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729 / 512) = 1/(512 / 729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (176674553 / 500000000) (353349107 / 1000000000) (Real.log (729 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (729 / 512) = -Real.log (512 / 729) := by
    rw [show ((729 / 512) : ℝ) = ((512 / 729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (137837317 / 250000000) ≤ -Real.log (295 / 512) ∧
    -Real.log (295 / 512) ≤ (551349269 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 807)) (n := 12)
    (lo := (137837317 / 250000000)) (hi := (551349269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 295) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 295) = 1/(295 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-551349269 / 1000000000) (-137837317 / 250000000) (Real.log (295 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (615185639 / 1000000000) ≤ -Real.log (20 / 37) ∧
    -Real.log (20 / 37) ≤ (15379641 / 25000000) := by
  have h := checkLog_sound (w := (17 / 57)) (n := 12)
    (lo := (615185639 / 1000000000)) (hi := (15379641 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37 / 20) = 1/(20 / 37) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (615185639 / 1000000000) (15379641 / 25000000) (Real.log (37 / 20)) := by
  have h := reflection_log_5_neg
  have he : Real.log (37 / 20) = -Real.log (20 / 37) := by
    rw [show ((37 / 20) : ℝ) = ((20 / 37) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1897119983 / 1000000000) ≤ -Real.log (3 / 20) ∧
    -Real.log (3 / 20) ≤ (948559993 / 500000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(5 / 3) = 1/(3 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-948559993 / 500000000) (-1897119983 / 1000000000) (Real.log (3 / 20)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (76739743 / 125000000) ≤ -Real.log (256 / 473) ∧
    -Real.log (256 / 473) ≤ (122783589 / 200000000) := by
  have h := checkLog_sound (w := (217 / 729)) (n := 12)
    (lo := (76739743 / 125000000)) (hi := (122783589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473 / 256) = 1/(256 / 473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (76739743 / 125000000) (122783589 / 200000000) (Real.log (473 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (473 / 256) = -Real.log (256 / 473) := by
    rw [show ((473 / 256) : ℝ) = ((256 / 473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1881615797 / 1000000000) ≤ -Real.log (39 / 256) ∧
    -Real.log (39 / 256) ≤ (9408079 / 5000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 39) = 1/(39 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9408079 / 5000000) (-1881615797 / 1000000000) (Real.log (39 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (97326667 / 200000000) ≤ -Real.log (100000 / 162683) ∧
    -Real.log (100000 / 162683) ≤ (60829167 / 125000000) := by
  have h := checkLog_sound (w := (62683 / 262683)) (n := 12)
    (lo := (97326667 / 200000000)) (hi := (60829167 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162683 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162683 / 100000) = 1/(100000 / 162683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (97326667 / 200000000) (60829167 / 125000000) (Real.log (162683 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (162683 / 100000) = -Real.log (100000 / 162683) := by
    rw [show ((162683 / 100000) : ℝ) = ((100000 / 162683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (492860599 / 500000000) ≤ -Real.log (37317 / 100000) ∧
    -Real.log (37317 / 100000) ≤ (2464303 / 2500000) := by
  have h := checkLog_sound (w := (12683 / 87317)) (n := 12)
    (lo := (146287009 / 500000000)) (hi := (292574019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 37317) = 1/(37317 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2464303 / 2500000) (-492860599 / 500000000) (Real.log (37317 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (121963803 / 250000000) ≤ -Real.log (1000000 / 1628819) ∧
    -Real.log (1000000 / 1628819) ≤ (487855213 / 1000000000) := by
  have h := checkLog_sound (w := (628819 / 2628819)) (n := 12)
    (lo := (121963803 / 250000000)) (hi := (487855213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1628819 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1628819 / 1000000) = 1/(1000000 / 1628819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (121963803 / 250000000) (487855213 / 1000000000) (Real.log (1628819 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1628819 / 1000000) = -Real.log (1000000 / 1628819) := by
    rw [show ((1628819 / 1000000) : ℝ) = ((1000000 / 1628819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (123883183 / 125000000) ≤ -Real.log (371181 / 1000000) ∧
    -Real.log (371181 / 1000000) ≤ (495532733 / 500000000) := by
  have h := checkLog_sound (w := (128819 / 871181)) (n := 12)
    (lo := (74479571 / 250000000)) (hi := (59583657 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371181) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 371181) = 1/(371181 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-495532733 / 500000000) (-123883183 / 125000000) (Real.log (371181 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (403328159 / 1000000000) ≤ -Real.log (500000 / 748399) ∧
    -Real.log (500000 / 748399) ≤ (2520801 / 6250000) := by
  have h := checkLog_sound (w := (248399 / 1248399)) (n := 12)
    (lo := (403328159 / 1000000000)) (hi := (2520801 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748399 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748399 / 500000) = 1/(500000 / 748399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (403328159 / 1000000000) (2520801 / 6250000) (Real.log (748399 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (748399 / 500000) = -Real.log (500000 / 748399) := by
    rw [show ((748399 / 500000) : ℝ) = ((500000 / 748399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (686763599 / 1000000000) ≤ -Real.log (251601 / 500000) ∧
    -Real.log (251601 / 500000) ≤ (1716909 / 2500000) := by
  have h := checkLog_sound (w := (248399 / 751601)) (n := 12)
    (lo := (686763599 / 1000000000)) (hi := (1716909 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 251601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 251601) = 1/(251601 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1716909 / 2500000) (-686763599 / 1000000000) (Real.log (251601 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (202316047 / 500000000) ≤ -Real.log (1000000 / 1498751) ∧
    -Real.log (1000000 / 1498751) ≤ (80926419 / 200000000) := by
  have h := checkLog_sound (w := (498751 / 2498751)) (n := 12)
    (lo := (202316047 / 500000000)) (hi := (80926419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1498751 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1498751 / 1000000) = 1/(1000000 / 1498751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (202316047 / 500000000) (80926419 / 200000000) (Real.log (1498751 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1498751 / 1000000) = -Real.log (1000000 / 1498751) := by
    rw [show ((1498751 / 1000000) : ℝ) = ((1000000 / 1498751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (138130459 / 200000000) ≤ -Real.log (501249 / 1000000) ∧
    -Real.log (501249 / 1000000) ≤ (86331537 / 125000000) := by
  have h := checkLog_sound (w := (498751 / 1501249)) (n := 12)
    (lo := (138130459 / 200000000)) (hi := (86331537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 501249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 501249) = 1/(501249 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-86331537 / 125000000) (-138130459 / 200000000) (Real.log (501249 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1472354533 / 1000000000) ≤ -Real.log (500000000000 / 2179743816491) ∧
    -Real.log (500000000000 / 2179743816491) ≤ (184044317 / 125000000) := by
  have h := checkLog_sound (w := (179743816491 / 4179743816491)) (n := 12)
    (lo := (86060173 / 1000000000)) (hi := (43030087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2179743816491 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2179743816491 / 2000000000000) = 1/(500000000000 / 2179743816491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1472354533 / 1000000000) (184044317 / 125000000) (Real.log (2179743816491 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2179743816491 / 500000000000) = -Real.log (500000000000 / 2179743816491) := by
    rw [show ((2179743816491 / 500000000000) : ℝ) = ((500000000000 / 2179743816491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (59156827 / 40000000) ≤ -Real.log (250000000000 / 1097051707927) ∧
    -Real.log (250000000000 / 1097051707927) ≤ (739460339 / 500000000) := by
  have h := checkLog_sound (w := (97051707927 / 2097051707927)) (n := 12)
    (lo := (18525263 / 200000000)) (hi := (23156579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097051707927 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1097051707927 / 1000000000000) = 1/(250000000000 / 1097051707927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (59156827 / 40000000) (739460339 / 500000000) (Real.log (1097051707927 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1097051707927 / 250000000000) = -Real.log (250000000000 / 1097051707927) := by
    rw [show ((1097051707927 / 250000000000) : ℝ) = ((250000000000 / 1097051707927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (545045879 / 500000000) ≤ -Real.log (250000000000 / 743636750251) ∧
    -Real.log (250000000000 / 743636750251) ≤ (13626147 / 12500000) := by
  have h := checkLog_sound (w := (243636750251 / 1243636750251)) (n := 12)
    (lo := (198472289 / 500000000)) (hi := (396944579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743636750251 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(743636750251 / 500000000000) = 1/(250000000000 / 743636750251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (545045879 / 500000000) (13626147 / 12500000) (Real.log (743636750251 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (743636750251 / 250000000000) = -Real.log (250000000000 / 743636750251) := by
    rw [show ((743636750251 / 250000000000) : ℝ) = ((250000000000 / 743636750251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1095284389 / 1000000000) ≤ -Real.log (500000000000 / 1495016448911) ∧
    -Real.log (500000000000 / 1495016448911) ≤ (1095284391 / 1000000000) := by
  have h := checkLog_sound (w := (495016448911 / 2495016448911)) (n := 12)
    (lo := (402137209 / 1000000000)) (hi := (40213721 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1495016448911 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1495016448911 / 1000000000000) = 1/(500000000000 / 1495016448911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1095284389 / 1000000000) (1095284391 / 1000000000) (Real.log (1495016448911 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1495016448911 / 500000000000) = -Real.log (500000000000 / 1495016448911) := by
    rw [show ((1495016448911 / 500000000000) : ℝ) = ((500000000000 / 1495016448911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0075

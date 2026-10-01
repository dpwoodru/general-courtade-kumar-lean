import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0065
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

theorem reflection_log_1_neg : (362361867 / 1000000000) ≤ -Real.log (1280 / 1839) ∧
    -Real.log (1280 / 1839) ≤ (90590467 / 250000000) := by
  have h := checkLog_sound (w := (559 / 3119)) (n := 12)
    (lo := (362361867 / 1000000000)) (hi := (90590467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1839 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1839 / 1280) = 1/(1280 / 1839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (362361867 / 1000000000) (90590467 / 250000000) (Real.log (1839 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1839 / 1280) = -Real.log (1280 / 1839) := by
    rw [show ((1839 / 1280) : ℝ) = ((1280 / 1839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (573976219 / 1000000000) ≤ -Real.log (721 / 1280) ∧
    -Real.log (721 / 1280) ≤ (28698811 / 50000000) := by
  have h := checkLog_sound (w := (559 / 2001)) (n := 12)
    (lo := (573976219 / 1000000000)) (hi := (28698811 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 721) = 1/(721 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-28698811 / 50000000) (-573976219 / 1000000000) (Real.log (721 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (180772937 / 500000000) ≤ -Real.log (512 / 735) ∧
    -Real.log (512 / 735) ≤ (2892367 / 8000000) := by
  have h := checkLog_sound (w := (223 / 1247)) (n := 12)
    (lo := (180772937 / 500000000)) (hi := (2892367 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735 / 512) = 1/(512 / 735) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (180772937 / 500000000) (2892367 / 8000000) (Real.log (735 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (735 / 512) = -Real.log (512 / 735) := by
    rw [show ((735 / 512) : ℝ) = ((512 / 735) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (35743621 / 62500000) ≤ -Real.log (289 / 512) ∧
    -Real.log (289 / 512) ≤ (571897937 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 801)) (n := 12)
    (lo := (35743621 / 62500000)) (hi := (571897937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 289) = 1/(289 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-571897937 / 1000000000) (-35743621 / 62500000) (Real.log (289 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (313887489 / 500000000) ≤ -Real.log (640 / 1199) ∧
    -Real.log (640 / 1199) ≤ (627774979 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 1839)) (n := 12)
    (lo := (313887489 / 500000000)) (hi := (627774979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199 / 640) = 1/(640 / 1199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (313887489 / 500000000) (627774979 / 1000000000) (Real.log (1199 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1199 / 640) = -Real.log (640 / 1199) := by
    rw [show ((1199 / 640) : ℝ) = ((640 / 1199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (103350951 / 50000000) ≤ -Real.log (81 / 640) ∧
    -Real.log (81 / 640) ≤ (2067019023 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 81) = 1/(81 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2067019023 / 1000000000) (-103350951 / 50000000) (Real.log (81 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (39157697 / 62500000) ≤ -Real.log (256 / 479) ∧
    -Real.log (256 / 479) ≤ (626523153 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 735)) (n := 12)
    (lo := (39157697 / 62500000)) (hi := (626523153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479 / 256) = 1/(256 / 479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (39157697 / 62500000) (626523153 / 1000000000) (Real.log (479 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (479 / 256) = -Real.log (256 / 479) := by
    rw [show ((479 / 256) : ℝ) = ((256 / 479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2048669881 / 1000000000) ≤ -Real.log (33 / 256) ∧
    -Real.log (33 / 256) ≤ (512167471 / 250000000) := by
  have h := checkLog_sound (w := (31 / 97)) (n := 12)
    (lo := (662375521 / 1000000000)) (hi := (331187761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 33) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 33) = 1/(33 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-512167471 / 250000000) (-2048669881 / 1000000000) (Real.log (33 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (124728237 / 250000000) ≤ -Real.log (100000 / 164693) ∧
    -Real.log (100000 / 164693) ≤ (498912949 / 1000000000) := by
  have h := checkLog_sound (w := (64693 / 264693)) (n := 12)
    (lo := (124728237 / 250000000)) (hi := (498912949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164693 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164693 / 100000) = 1/(100000 / 164693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (124728237 / 250000000) (498912949 / 1000000000) (Real.log (164693 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (164693 / 100000) = -Real.log (100000 / 164693) := by
    rw [show ((164693 / 100000) : ℝ) = ((100000 / 164693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (52054447 / 50000000) ≤ -Real.log (35307 / 100000) ∧
    -Real.log (35307 / 100000) ≤ (520544471 / 500000000) := by
  have h := checkLog_sound (w := (14693 / 85307)) (n := 12)
    (lo := (543659 / 1562500)) (hi := (347941761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35307) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35307) = 1/(35307 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-520544471 / 500000000) (-52054447 / 50000000) (Real.log (35307 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (10003017 / 20000000) ≤ -Real.log (100000 / 164897) ∧
    -Real.log (100000 / 164897) ≤ (500150851 / 1000000000) := by
  have h := checkLog_sound (w := (64897 / 264897)) (n := 12)
    (lo := (10003017 / 20000000)) (hi := (500150851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164897 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164897 / 100000) = 1/(100000 / 164897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (10003017 / 20000000) (500150851 / 1000000000) (Real.log (164897 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (164897 / 100000) = -Real.log (100000 / 164897) := by
    rw [show ((164897 / 100000) : ℝ) = ((100000 / 164897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (261720897 / 250000000) ≤ -Real.log (35103 / 100000) ∧
    -Real.log (35103 / 100000) ≤ (104688359 / 100000000) := by
  have h := checkLog_sound (w := (14897 / 85103)) (n := 12)
    (lo := (44217051 / 125000000)) (hi := (353736409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35103) = 1/(35103 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-104688359 / 100000000) (-261720897 / 250000000) (Real.log (35103 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (416548789 / 1000000000) ≤ -Real.log (500000 / 758359) ∧
    -Real.log (500000 / 758359) ≤ (41654879 / 100000000) := by
  have h := checkLog_sound (w := (258359 / 1258359)) (n := 12)
    (lo := (416548789 / 1000000000)) (hi := (41654879 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758359 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(758359 / 500000) = 1/(500000 / 758359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (416548789 / 1000000000) (41654879 / 100000000) (Real.log (758359 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (758359 / 500000) = -Real.log (500000 / 758359) := by
    rw [show ((758359 / 500000) : ℝ) = ((500000 / 758359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2840449 / 3906250) ≤ -Real.log (241641 / 500000) ∧
    -Real.log (241641 / 500000) ≤ (363577473 / 500000000) := by
  have h := checkLog_sound (w := (8359 / 491641)) (n := 12)
    (lo := (8501941 / 250000000)) (hi := (6801553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 241641) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 241641) = 1/(241641 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-363577473 / 500000000) (-2840449 / 3906250) (Real.log (241641 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (417896187 / 1000000000) ≤ -Real.log (1000000 / 1518763) ∧
    -Real.log (1000000 / 1518763) ≤ (104474047 / 250000000) := by
  have h := checkLog_sound (w := (518763 / 2518763)) (n := 12)
    (lo := (417896187 / 1000000000)) (hi := (104474047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1518763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1518763 / 1000000) = 1/(1000000 / 1518763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (417896187 / 1000000000) (104474047 / 250000000) (Real.log (1518763 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1518763 / 1000000) = -Real.log (1000000 / 1518763) := by
    rw [show ((1518763 / 1000000) : ℝ) = ((1000000 / 1518763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (365697703 / 500000000) ≤ -Real.log (481237 / 1000000) ∧
    -Real.log (481237 / 1000000) ≤ (45712213 / 62500000) := by
  have h := checkLog_sound (w := (18763 / 981237)) (n := 12)
    (lo := (19124113 / 500000000)) (hi := (38248227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 481237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 481237) = 1/(481237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-45712213 / 62500000) (-365697703 / 500000000) (Real.log (481237 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1540001889 / 1000000000) ≤ -Real.log (500000000000 / 2332299543999) ∧
    -Real.log (500000000000 / 2332299543999) ≤ (385000473 / 250000000) := by
  have h := checkLog_sound (w := (332299543999 / 4332299543999)) (n := 12)
    (lo := (153707529 / 1000000000)) (hi := (15370753 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2332299543999 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2332299543999 / 2000000000000) = 1/(500000000000 / 2332299543999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1540001889 / 1000000000) (385000473 / 250000000) (Real.log (2332299543999 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2332299543999 / 500000000000) = -Real.log (500000000000 / 2332299543999) := by
    rw [show ((2332299543999 / 500000000000) : ℝ) = ((500000000000 / 2332299543999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (773517219 / 500000000) ≤ -Real.log (500000000000 / 2348759365297) ∧
    -Real.log (500000000000 / 2348759365297) ≤ (1547034441 / 1000000000) := by
  have h := checkLog_sound (w := (348759365297 / 4348759365297)) (n := 12)
    (lo := (80370039 / 500000000)) (hi := (160740079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2348759365297 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2348759365297 / 2000000000000) = 1/(500000000000 / 2348759365297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (773517219 / 500000000) (1547034441 / 1000000000) (Real.log (2348759365297 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2348759365297 / 500000000000) = -Real.log (500000000000 / 2348759365297) := by
    rw [show ((2348759365297 / 500000000000) : ℝ) = ((500000000000 / 2348759365297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (571851867 / 500000000) ≤ -Real.log (125000000000 / 392296319747) ∧
    -Real.log (125000000000 / 392296319747) ≤ (142962967 / 125000000) := by
  have h := checkLog_sound (w := (142296319747 / 642296319747)) (n := 12)
    (lo := (225278277 / 500000000)) (hi := (90111311 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392296319747 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(392296319747 / 250000000000) = 1/(125000000000 / 392296319747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (571851867 / 500000000) (142962967 / 125000000) (Real.log (392296319747 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (392296319747 / 125000000000) = -Real.log (125000000000 / 392296319747) := by
    rw [show ((392296319747 / 125000000000) : ℝ) = ((125000000000 / 392296319747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1149291593 / 1000000000) ≤ -Real.log (500000000000 / 1577978210321) ∧
    -Real.log (500000000000 / 1577978210321) ≤ (229858319 / 200000000) := by
  have h := checkLog_sound (w := (577978210321 / 2577978210321)) (n := 12)
    (lo := (456144413 / 1000000000)) (hi := (228072207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1577978210321 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1577978210321 / 1000000000000) = 1/(500000000000 / 1577978210321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1149291593 / 1000000000) (229858319 / 200000000) (Real.log (1577978210321 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1577978210321 / 500000000000) = -Real.log (500000000000 / 1577978210321) := by
    rw [show ((1577978210321 / 500000000000) : ℝ) = ((500000000000 / 1577978210321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0065

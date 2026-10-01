import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0310
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

theorem reflection_log_1_neg : (221579829 / 1000000000) ≤ -Real.log (512 / 639) ∧
    -Real.log (512 / 639) ≤ (22157983 / 100000000) := by
  have h := checkLog_sound (w := (127 / 1151)) (n := 12)
    (lo := (221579829 / 1000000000)) (hi := (22157983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639 / 512) = 1/(512 / 639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (221579829 / 1000000000) (22157983 / 100000000) (Real.log (639 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (639 / 512) = -Real.log (512 / 639) := by
    rw [show ((639 / 512) : ℝ) = ((512 / 639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (28508129 / 100000000) ≤ -Real.log (385 / 512) ∧
    -Real.log (385 / 512) ≤ (285081291 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 897)) (n := 12)
    (lo := (28508129 / 100000000)) (hi := (285081291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 385) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 385) = 1/(385 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-285081291 / 1000000000) (-28508129 / 100000000) (Real.log (385 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (221345059 / 1000000000) ≤ -Real.log (10240 / 12777) ∧
    -Real.log (10240 / 12777) ≤ (11067253 / 50000000) := by
  have h := checkLog_sound (w := (2537 / 23017)) (n := 12)
    (lo := (221345059 / 1000000000)) (hi := (11067253 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12777 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12777 / 10240) = 1/(10240 / 12777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (221345059 / 1000000000) (11067253 / 50000000) (Real.log (12777 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12777 / 10240) = -Real.log (10240 / 12777) := by
    rw [show ((12777 / 10240) : ℝ) = ((10240 / 12777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (71172939 / 250000000) ≤ -Real.log (7703 / 10240) ∧
    -Real.log (7703 / 10240) ≤ (284691757 / 1000000000) := by
  have h := checkLog_sound (w := (2537 / 17943)) (n := 12)
    (lo := (71172939 / 250000000)) (hi := (284691757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7703) = 1/(7703 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-284691757 / 1000000000) (-71172939 / 250000000) (Real.log (7703 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (50357193 / 125000000) ≤ -Real.log (256 / 383) ∧
    -Real.log (256 / 383) ≤ (80571509 / 200000000) := by
  have h := checkLog_sound (w := (127 / 639)) (n := 12)
    (lo := (50357193 / 125000000)) (hi := (80571509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383 / 256) = 1/(256 / 383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (50357193 / 125000000) (80571509 / 200000000) (Real.log (383 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (383 / 256) = -Real.log (256 / 383) := by
    rw [show ((383 / 256) : ℝ) = ((256 / 383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (8567063 / 12500000) ≤ -Real.log (129 / 256) ∧
    -Real.log (129 / 256) ≤ (685365041 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 385)) (n := 12)
    (lo := (8567063 / 12500000)) (hi := (685365041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 129) = 1/(129 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-685365041 / 1000000000) (-8567063 / 12500000) (Real.log (129 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (402465823 / 1000000000) ≤ -Real.log (5120 / 7657) ∧
    -Real.log (5120 / 7657) ≤ (12577057 / 31250000) := by
  have h := checkLog_sound (w := (2537 / 12777)) (n := 12)
    (lo := (402465823 / 1000000000)) (hi := (12577057 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7657 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7657 / 5120) = 1/(5120 / 7657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (402465823 / 1000000000) (12577057 / 31250000) (Real.log (7657 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7657 / 5120) = -Real.log (5120 / 7657) := by
    rw [show ((7657 / 5120) : ℝ) = ((5120 / 7657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (171050731 / 250000000) ≤ -Real.log (2583 / 5120) ∧
    -Real.log (2583 / 5120) ≤ (27368117 / 40000000) := by
  have h := checkLog_sound (w := (2537 / 7703)) (n := 12)
    (lo := (171050731 / 250000000)) (hi := (27368117 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2583) = 1/(2583 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-27368117 / 40000000) (-171050731 / 250000000) (Real.log (2583 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (303345261 / 1000000000) ≤ -Real.log (500000 / 677191) ∧
    -Real.log (500000 / 677191) ≤ (151672631 / 500000000) := by
  have h := checkLog_sound (w := (177191 / 1177191)) (n := 12)
    (lo := (303345261 / 1000000000)) (hi := (151672631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677191 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677191 / 500000) = 1/(500000 / 677191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (303345261 / 1000000000) (151672631 / 500000000) (Real.log (677191 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (677191 / 500000) = -Real.log (500000 / 677191) := by
    rw [show ((677191 / 500000) : ℝ) = ((500000 / 677191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (437547281 / 1000000000) ≤ -Real.log (322809 / 500000) ∧
    -Real.log (322809 / 500000) ≤ (218773641 / 500000000) := by
  have h := checkLog_sound (w := (177191 / 822809)) (n := 12)
    (lo := (437547281 / 1000000000)) (hi := (218773641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 322809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 322809) = 1/(322809 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-218773641 / 500000000) (-437547281 / 1000000000) (Real.log (322809 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (303663437 / 1000000000) ≤ -Real.log (1000000 / 1354813) ∧
    -Real.log (1000000 / 1354813) ≤ (151831719 / 500000000) := by
  have h := checkLog_sound (w := (354813 / 2354813)) (n := 12)
    (lo := (303663437 / 1000000000)) (hi := (151831719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1354813 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1354813 / 1000000) = 1/(1000000 / 1354813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (303663437 / 1000000000) (151831719 / 500000000) (Real.log (1354813 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1354813 / 1000000) = -Real.log (1000000 / 1354813) := by
    rw [show ((1354813 / 1000000) : ℝ) = ((1000000 / 1354813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (438215081 / 1000000000) ≤ -Real.log (645187 / 1000000) ∧
    -Real.log (645187 / 1000000) ≤ (219107541 / 500000000) := by
  have h := checkLog_sound (w := (354813 / 1645187)) (n := 12)
    (lo := (438215081 / 1000000000)) (hi := (219107541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 645187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 645187) = 1/(645187 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-219107541 / 500000000) (-438215081 / 1000000000) (Real.log (645187 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (230799767 / 1000000000) ≤ -Real.log (1000000 / 1259607) ∧
    -Real.log (1000000 / 1259607) ≤ (28849971 / 125000000) := by
  have h := checkLog_sound (w := (259607 / 2259607)) (n := 12)
    (lo := (230799767 / 1000000000)) (hi := (28849971 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259607 / 1000000) = 1/(1000000 / 1259607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (230799767 / 1000000000) (28849971 / 125000000) (Real.log (1259607 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1259607 / 1000000) = -Real.log (1000000 / 1259607) := by
    rw [show ((1259607 / 1000000) : ℝ) = ((1000000 / 1259607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (37571769 / 125000000) ≤ -Real.log (740393 / 1000000) ∧
    -Real.log (740393 / 1000000) ≤ (300574153 / 1000000000) := by
  have h := checkLog_sound (w := (259607 / 1740393)) (n := 12)
    (lo := (37571769 / 125000000)) (hi := (300574153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 740393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 740393) = 1/(740393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-300574153 / 1000000000) (-37571769 / 125000000) (Real.log (740393 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (231068069 / 1000000000) ≤ -Real.log (200000 / 251989) ∧
    -Real.log (200000 / 251989) ≤ (23106807 / 100000000) := by
  have h := checkLog_sound (w := (51989 / 451989)) (n := 12)
    (lo := (231068069 / 1000000000)) (hi := (23106807 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251989 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251989 / 200000) = 1/(200000 / 251989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (231068069 / 1000000000) (23106807 / 100000000) (Real.log (251989 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (251989 / 200000) = -Real.log (200000 / 251989) := by
    rw [show ((251989 / 200000) : ℝ) = ((200000 / 251989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (301030771 / 1000000000) ≤ -Real.log (148011 / 200000) ∧
    -Real.log (148011 / 200000) ≤ (75257693 / 250000000) := by
  have h := checkLog_sound (w := (51989 / 348011)) (n := 12)
    (lo := (301030771 / 1000000000)) (hi := (75257693 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148011) = 1/(148011 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-75257693 / 250000000) (-301030771 / 1000000000) (Real.log (148011 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (370446271 / 500000000) ≤ -Real.log (50000000000 / 104890353119) ∧
    -Real.log (50000000000 / 104890353119) ≤ (5788223 / 7812500) := by
  have h := checkLog_sound (w := (4890353119 / 204890353119)) (n := 12)
    (lo := (23872681 / 500000000)) (hi := (47745363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104890353119 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(104890353119 / 100000000000) = 1/(50000000000 / 104890353119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (370446271 / 500000000) (5788223 / 7812500) (Real.log (104890353119 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (104890353119 / 50000000000) = -Real.log (50000000000 / 104890353119) := by
    rw [show ((104890353119 / 50000000000) : ℝ) = ((50000000000 / 104890353119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (370939259 / 500000000) ≤ -Real.log (250000000000 / 524969117481) ∧
    -Real.log (250000000000 / 524969117481) ≤ (18546963 / 25000000) := by
  have h := checkLog_sound (w := (24969117481 / 1024969117481)) (n := 12)
    (lo := (24365669 / 500000000)) (hi := (48731339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((524969117481 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(524969117481 / 500000000000) = 1/(250000000000 / 524969117481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (370939259 / 500000000) (18546963 / 25000000) (Real.log (524969117481 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (524969117481 / 250000000000) = -Real.log (250000000000 / 524969117481) := by
    rw [show ((524969117481 / 250000000000) : ℝ) = ((250000000000 / 524969117481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3321087 / 6250000) ≤ -Real.log (500000000000 / 850634055157) ∧
    -Real.log (500000000000 / 850634055157) ≤ (531373921 / 1000000000) := by
  have h := checkLog_sound (w := (350634055157 / 1350634055157)) (n := 12)
    (lo := (3321087 / 6250000)) (hi := (531373921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850634055157 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850634055157 / 500000000000) = 1/(500000000000 / 850634055157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3321087 / 6250000) (531373921 / 1000000000) (Real.log (850634055157 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (850634055157 / 500000000000) = -Real.log (500000000000 / 850634055157) := by
    rw [show ((850634055157 / 500000000000) : ℝ) = ((500000000000 / 850634055157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (13302471 / 25000000) ≤ -Real.log (25000000000 / 42562546027) ∧
    -Real.log (25000000000 / 42562546027) ≤ (532098841 / 1000000000) := by
  have h := checkLog_sound (w := (17562546027 / 67562546027)) (n := 12)
    (lo := (13302471 / 25000000)) (hi := (532098841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42562546027 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42562546027 / 25000000000) = 1/(25000000000 / 42562546027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (13302471 / 25000000) (532098841 / 1000000000) (Real.log (42562546027 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (42562546027 / 25000000000) = -Real.log (25000000000 / 42562546027) := by
    rw [show ((42562546027 / 25000000000) : ℝ) = ((25000000000 / 42562546027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0310

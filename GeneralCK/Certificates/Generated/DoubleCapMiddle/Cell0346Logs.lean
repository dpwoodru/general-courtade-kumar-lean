import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0346
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

theorem reflection_log_1_neg : (42618643 / 200000000) ≤ -Real.log (80 / 99) ∧
    -Real.log (80 / 99) ≤ (6659163 / 31250000) := by
  have h := checkLog_sound (w := (19 / 179)) (n := 12)
    (lo := (42618643 / 200000000)) (hi := (6659163 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99 / 80) = 1/(80 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42618643 / 200000000) (6659163 / 31250000) (Real.log (99 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (99 / 80) = -Real.log (80 / 99) := by
    rw [show ((99 / 80) : ℝ) = ((80 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (27115277 / 100000000) ≤ -Real.log (61 / 80) ∧
    -Real.log (61 / 80) ≤ (271152771 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 141)) (n := 12)
    (lo := (27115277 / 100000000)) (hi := (271152771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 61) = 1/(61 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-271152771 / 1000000000) (-27115277 / 100000000) (Real.log (61 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42571289 / 200000000) ≤ -Real.log (10240 / 12669) ∧
    -Real.log (10240 / 12669) ≤ (106428223 / 500000000) := by
  have h := checkLog_sound (w := (2429 / 22909)) (n := 12)
    (lo := (42571289 / 200000000)) (hi := (106428223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12669 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12669 / 10240) = 1/(10240 / 12669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42571289 / 200000000) (106428223 / 500000000) (Real.log (12669 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12669 / 10240) = -Real.log (10240 / 12669) := by
    rw [show ((12669 / 10240) : ℝ) = ((10240 / 12669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (135384311 / 500000000) ≤ -Real.log (7811 / 10240) ∧
    -Real.log (7811 / 10240) ≤ (270768623 / 1000000000) := by
  have h := checkLog_sound (w := (2429 / 18051)) (n := 12)
    (lo := (135384311 / 500000000)) (hi := (270768623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7811) = 1/(7811 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-270768623 / 1000000000) (-135384311 / 500000000) (Real.log (7811 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (388657989 / 1000000000) ≤ -Real.log (40 / 59) ∧
    -Real.log (40 / 59) ≤ (38865799 / 100000000) := by
  have h := checkLog_sound (w := (19 / 99)) (n := 12)
    (lo := (388657989 / 1000000000)) (hi := (38865799 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59 / 40) = 1/(40 / 59) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (388657989 / 1000000000) (38865799 / 100000000) (Real.log (59 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (59 / 40) = -Real.log (40 / 59) := by
    rw [show ((59 / 40) : ℝ) = ((40 / 59) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (80544627 / 125000000) ≤ -Real.log (21 / 40) ∧
    -Real.log (21 / 40) ≤ (644357017 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 21) = 1/(21 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-644357017 / 1000000000) (-80544627 / 125000000) (Real.log (21 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (77652133 / 200000000) ≤ -Real.log (5120 / 7549) ∧
    -Real.log (5120 / 7549) ≤ (194130333 / 500000000) := by
  have h := checkLog_sound (w := (2429 / 12669)) (n := 12)
    (lo := (77652133 / 200000000)) (hi := (194130333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7549 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7549 / 5120) = 1/(5120 / 7549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (77652133 / 200000000) (194130333 / 500000000) (Real.log (7549 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7549 / 5120) = -Real.log (5120 / 7549) := by
    rw [show ((7549 / 5120) : ℝ) = ((5120 / 7549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (643241567 / 1000000000) ≤ -Real.log (2691 / 5120) ∧
    -Real.log (2691 / 5120) ≤ (20101299 / 31250000) := by
  have h := checkLog_sound (w := (2429 / 7811)) (n := 12)
    (lo := (643241567 / 1000000000)) (hi := (20101299 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2691) = 1/(2691 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20101299 / 31250000) (-643241567 / 1000000000) (Real.log (2691 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (291879003 / 1000000000) ≤ -Real.log (1000000 / 1338941) ∧
    -Real.log (1000000 / 1338941) ≤ (72969751 / 250000000) := by
  have h := checkLog_sound (w := (338941 / 2338941)) (n := 12)
    (lo := (291879003 / 1000000000)) (hi := (72969751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1338941 / 1000000) = 1/(1000000 / 1338941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (291879003 / 1000000000) (72969751 / 250000000) (Real.log (1338941 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1338941 / 1000000) = -Real.log (1000000 / 1338941) := by
    rw [show ((1338941 / 1000000) : ℝ) = ((1000000 / 1338941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (51739023 / 125000000) ≤ -Real.log (661059 / 1000000) ∧
    -Real.log (661059 / 1000000) ≤ (82782437 / 200000000) := by
  have h := checkLog_sound (w := (338941 / 1661059)) (n := 12)
    (lo := (51739023 / 125000000)) (hi := (82782437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 661059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 661059) = 1/(661059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-82782437 / 200000000) (-51739023 / 125000000) (Real.log (661059 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (2922001 / 10000000) ≤ -Real.log (1000000 / 1339371) ∧
    -Real.log (1000000 / 1339371) ≤ (292200101 / 1000000000) := by
  have h := checkLog_sound (w := (339371 / 2339371)) (n := 12)
    (lo := (2922001 / 10000000)) (hi := (292200101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1339371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1339371 / 1000000) = 1/(1000000 / 1339371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (2922001 / 10000000) (292200101 / 1000000000) (Real.log (1339371 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1339371 / 1000000) = -Real.log (1000000 / 1339371) := by
    rw [show ((1339371 / 1000000) : ℝ) = ((1000000 / 1339371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (414562867 / 1000000000) ≤ -Real.log (660629 / 1000000) ∧
    -Real.log (660629 / 1000000) ≤ (103640717 / 250000000) := by
  have h := checkLog_sound (w := (339371 / 1660629)) (n := 12)
    (lo := (414562867 / 1000000000)) (hi := (103640717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 660629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 660629) = 1/(660629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-103640717 / 250000000) (-414562867 / 1000000000) (Real.log (660629 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (221171207 / 1000000000) ≤ -Real.log (1000000 / 1247537) ∧
    -Real.log (1000000 / 1247537) ≤ (27646401 / 125000000) := by
  have h := checkLog_sound (w := (247537 / 2247537)) (n := 12)
    (lo := (221171207 / 1000000000)) (hi := (27646401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247537 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247537 / 1000000) = 1/(1000000 / 1247537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (221171207 / 1000000000) (27646401 / 125000000) (Real.log (1247537 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1247537 / 1000000) = -Real.log (1000000 / 1247537) := by
    rw [show ((1247537 / 1000000) : ℝ) = ((1000000 / 1247537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (284403453 / 1000000000) ≤ -Real.log (752463 / 1000000) ∧
    -Real.log (752463 / 1000000) ≤ (142201727 / 500000000) := by
  have h := checkLog_sound (w := (247537 / 1752463)) (n := 12)
    (lo := (284403453 / 1000000000)) (hi := (142201727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 752463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 752463) = 1/(752463 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-142201727 / 500000000) (-284403453 / 1000000000) (Real.log (752463 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (2214397 / 10000000) ≤ -Real.log (15625 / 19498) ∧
    -Real.log (15625 / 19498) ≤ (221439701 / 1000000000) := by
  have h := checkLog_sound (w := (3873 / 35123)) (n := 12)
    (lo := (2214397 / 10000000)) (hi := (221439701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19498 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19498 / 15625) = 1/(15625 / 19498) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (2214397 / 10000000) (221439701 / 1000000000) (Real.log (19498 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (19498 / 15625) = -Real.log (15625 / 19498) := by
    rw [show ((19498 / 15625) : ℝ) = ((15625 / 19498) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (71212189 / 250000000) ≤ -Real.log (11752 / 15625) ∧
    -Real.log (11752 / 15625) ≤ (284848757 / 1000000000) := by
  have h := checkLog_sound (w := (3873 / 27377)) (n := 12)
    (lo := (71212189 / 250000000)) (hi := (284848757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11752) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11752) = 1/(11752 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-284848757 / 1000000000) (-71212189 / 250000000) (Real.log (11752 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (352895593 / 500000000) ≤ -Real.log (500000000000 / 1012724280283) ∧
    -Real.log (500000000000 / 1012724280283) ≤ (176447797 / 250000000) := by
  have h := checkLog_sound (w := (12724280283 / 2012724280283)) (n := 12)
    (lo := (6322003 / 500000000)) (hi := (12644007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1012724280283 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1012724280283 / 1000000000000) = 1/(500000000000 / 1012724280283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (352895593 / 500000000) (176447797 / 250000000) (Real.log (1012724280283 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1012724280283 / 500000000000) = -Real.log (500000000000 / 1012724280283) := by
    rw [show ((1012724280283 / 500000000000) : ℝ) = ((500000000000 / 1012724280283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (706762967 / 1000000000) ≤ -Real.log (62500000000 / 126713613087) ∧
    -Real.log (62500000000 / 126713613087) ≤ (706762969 / 1000000000) := by
  have h := checkLog_sound (w := (1713613087 / 251713613087)) (n := 12)
    (lo := (13615787 / 1000000000)) (hi := (3403947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126713613087 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126713613087 / 125000000000) = 1/(62500000000 / 126713613087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (706762967 / 1000000000) (706762969 / 1000000000) (Real.log (126713613087 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (126713613087 / 62500000000) = -Real.log (62500000000 / 126713613087) := by
    rw [show ((126713613087 / 62500000000) : ℝ) = ((62500000000 / 126713613087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25278733 / 50000000) ≤ -Real.log (25000000000 / 41448449957) ∧
    -Real.log (25000000000 / 41448449957) ≤ (505574661 / 1000000000) := by
  have h := checkLog_sound (w := (16448449957 / 66448449957)) (n := 12)
    (lo := (25278733 / 50000000)) (hi := (505574661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41448449957 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41448449957 / 25000000000) = 1/(25000000000 / 41448449957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (25278733 / 50000000) (505574661 / 1000000000) (Real.log (41448449957 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (41448449957 / 25000000000) = -Real.log (25000000000 / 41448449957) := by
    rw [show ((41448449957 / 25000000000) : ℝ) = ((25000000000 / 41448449957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (506288457 / 1000000000) ≤ -Real.log (2500000000 / 4147804629) ∧
    -Real.log (2500000000 / 4147804629) ≤ (253144229 / 500000000) := by
  have h := checkLog_sound (w := (1647804629 / 6647804629)) (n := 12)
    (lo := (506288457 / 1000000000)) (hi := (253144229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4147804629 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4147804629 / 2500000000) = 1/(2500000000 / 4147804629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (506288457 / 1000000000) (253144229 / 500000000) (Real.log (4147804629 / 2500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4147804629 / 2500000000) = -Real.log (2500000000 / 4147804629) := by
    rw [show ((4147804629 / 2500000000) : ℝ) = ((2500000000 / 4147804629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0346

import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0174
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

theorem reflection_log_1_neg : (277276559 / 1000000000) ≤ -Real.log (1280 / 1689) ∧
    -Real.log (1280 / 1689) ≤ (3465957 / 12500000) := by
  have h := checkLog_sound (w := (409 / 2969)) (n := 12)
    (lo := (277276559 / 1000000000)) (hi := (3465957 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1689 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1689 / 1280) = 1/(1280 / 1689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (277276559 / 1000000000) (3465957 / 12500000) (Real.log (1689 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1689 / 1280) = -Real.log (1280 / 1689) := by
    rw [show ((1689 / 1280) : ℝ) = ((1280 / 1689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19248669 / 50000000) ≤ -Real.log (871 / 1280) ∧
    -Real.log (871 / 1280) ≤ (384973381 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2151)) (n := 12)
    (lo := (19248669 / 50000000)) (hi := (384973381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 871) = 1/(871 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-384973381 / 1000000000) (-19248669 / 50000000) (Real.log (871 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (276832411 / 1000000000) ≤ -Real.log (5120 / 6753) ∧
    -Real.log (5120 / 6753) ≤ (69208103 / 250000000) := by
  have h := checkLog_sound (w := (1633 / 11873)) (n := 12)
    (lo := (276832411 / 1000000000)) (hi := (69208103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6753 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6753 / 5120) = 1/(5120 / 6753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (276832411 / 1000000000) (69208103 / 250000000) (Real.log (6753 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6753 / 5120) = -Real.log (5120 / 6753) := by
    rw [show ((6753 / 5120) : ℝ) = ((5120 / 6753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (384112671 / 1000000000) ≤ -Real.log (3487 / 5120) ∧
    -Real.log (3487 / 5120) ≤ (12003521 / 31250000) := by
  have h := checkLog_sound (w := (1633 / 8607)) (n := 12)
    (lo := (384112671 / 1000000000)) (hi := (12003521 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3487) = 1/(3487 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12003521 / 31250000) (-384112671 / 1000000000) (Real.log (3487 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (30882777 / 62500000) ≤ -Real.log (640 / 1049) ∧
    -Real.log (640 / 1049) ≤ (494124433 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 1689)) (n := 12)
    (lo := (30882777 / 62500000)) (hi := (494124433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1049 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1049 / 640) = 1/(640 / 1049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (30882777 / 62500000) (494124433 / 1000000000) (Real.log (1049 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1049 / 640) = -Real.log (640 / 1049) := by
    rw [show ((1049 / 640) : ℝ) = ((640 / 1049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (203810093 / 200000000) ≤ -Real.log (231 / 640) ∧
    -Real.log (231 / 640) ≤ (1019050467 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 231) = 1/(231 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1019050467 / 1000000000) (-203810093 / 200000000) (Real.log (231 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (493409209 / 1000000000) ≤ -Real.log (2560 / 4193) ∧
    -Real.log (2560 / 4193) ≤ (49340921 / 100000000) := by
  have h := checkLog_sound (w := (1633 / 6753)) (n := 12)
    (lo := (493409209 / 1000000000)) (hi := (49340921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4193 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4193 / 2560) = 1/(2560 / 4193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (493409209 / 1000000000) (49340921 / 100000000) (Real.log (4193 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4193 / 2560) = -Real.log (2560 / 4193) := by
    rw [show ((4193 / 2560) : ℝ) = ((2560 / 4193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1015808971 / 1000000000) ≤ -Real.log (927 / 2560) ∧
    -Real.log (927 / 2560) ≤ (1015808973 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 2207)) (n := 12)
    (lo := (322661791 / 1000000000)) (hi := (10083181 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 927) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 927) = 1/(927 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1015808973 / 1000000000) (-1015808971 / 1000000000) (Real.log (927 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (37869873 / 100000000) ≤ -Real.log (1000000 / 1460383) ∧
    -Real.log (1000000 / 1460383) ≤ (378698731 / 1000000000) := by
  have h := checkLog_sound (w := (460383 / 2460383)) (n := 12)
    (lo := (37869873 / 100000000)) (hi := (378698731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1460383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1460383 / 1000000) = 1/(1000000 / 1460383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (37869873 / 100000000) (378698731 / 1000000000) (Real.log (1460383 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1460383 / 1000000) = -Real.log (1000000 / 1460383) := by
    rw [show ((1460383 / 1000000) : ℝ) = ((1000000 / 1460383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (12337913 / 20000000) ≤ -Real.log (539617 / 1000000) ∧
    -Real.log (539617 / 1000000) ≤ (616895651 / 1000000000) := by
  have h := checkLog_sound (w := (460383 / 1539617)) (n := 12)
    (lo := (12337913 / 20000000)) (hi := (616895651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 539617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 539617) = 1/(539617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-616895651 / 1000000000) (-12337913 / 20000000) (Real.log (539617 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (379307289 / 1000000000) ≤ -Real.log (125000 / 182659) ∧
    -Real.log (125000 / 182659) ≤ (37930729 / 100000000) := by
  have h := checkLog_sound (w := (57659 / 307659)) (n := 12)
    (lo := (379307289 / 1000000000)) (hi := (37930729 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182659 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182659 / 125000) = 1/(125000 / 182659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (379307289 / 1000000000) (37930729 / 100000000) (Real.log (182659 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (182659 / 125000) = -Real.log (125000 / 182659) := by
    rw [show ((182659 / 125000) : ℝ) = ((125000 / 182659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (618544473 / 1000000000) ≤ -Real.log (67341 / 125000) ∧
    -Real.log (67341 / 125000) ≤ (309272237 / 500000000) := by
  have h := checkLog_sound (w := (57659 / 192341)) (n := 12)
    (lo := (618544473 / 1000000000)) (hi := (309272237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 67341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 67341) = 1/(67341 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-309272237 / 500000000) (-618544473 / 1000000000) (Real.log (67341 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9280291 / 31250000) ≤ -Real.log (500000 / 672887) ∧
    -Real.log (500000 / 672887) ≤ (296969313 / 1000000000) := by
  have h := checkLog_sound (w := (172887 / 1172887)) (n := 12)
    (lo := (9280291 / 31250000)) (hi := (296969313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((672887 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(672887 / 500000) = 1/(500000 / 672887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9280291 / 31250000) (296969313 / 1000000000) (Real.log (672887 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (672887 / 500000) = -Real.log (500000 / 672887) := by
    rw [show ((672887 / 500000) : ℝ) = ((500000 / 672887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (424302421 / 1000000000) ≤ -Real.log (327113 / 500000) ∧
    -Real.log (327113 / 500000) ≤ (212151211 / 500000000) := by
  have h := checkLog_sound (w := (172887 / 827113)) (n := 12)
    (lo := (424302421 / 1000000000)) (hi := (212151211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 327113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 327113) = 1/(327113 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-212151211 / 500000000) (-424302421 / 1000000000) (Real.log (327113 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (297527199 / 1000000000) ≤ -Real.log (40000 / 53861) ∧
    -Real.log (40000 / 53861) ≤ (371909 / 1250000) := by
  have h := checkLog_sound (w := (13861 / 93861)) (n := 12)
    (lo := (297527199 / 1000000000)) (hi := (371909 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53861 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53861 / 40000) = 1/(40000 / 53861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (297527199 / 1000000000) (371909 / 1250000) (Real.log (53861 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (53861 / 40000) = -Real.log (40000 / 53861) := by
    rw [show ((53861 / 40000) : ℝ) = ((40000 / 53861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (212725501 / 500000000) ≤ -Real.log (26139 / 40000) ∧
    -Real.log (26139 / 40000) ≤ (425451003 / 1000000000) := by
  have h := checkLog_sound (w := (13861 / 66139)) (n := 12)
    (lo := (212725501 / 500000000)) (hi := (425451003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26139) = 1/(26139 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-425451003 / 1000000000) (-212725501 / 500000000) (Real.log (26139 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (995594379 / 1000000000) ≤ -Real.log (500000000000 / 1353166227157) ∧
    -Real.log (500000000000 / 1353166227157) ≤ (995594381 / 1000000000) := by
  have h := checkLog_sound (w := (353166227157 / 2353166227157)) (n := 12)
    (lo := (302447199 / 1000000000)) (hi := (378059 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353166227157 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1353166227157 / 1000000000000) = 1/(500000000000 / 1353166227157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (995594379 / 1000000000) (995594381 / 1000000000) (Real.log (1353166227157 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1353166227157 / 500000000000) = -Real.log (500000000000 / 1353166227157) := by
    rw [show ((1353166227157 / 500000000000) : ℝ) = ((500000000000 / 1353166227157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (498925881 / 500000000) ≤ -Real.log (250000000000 / 678112145647) ∧
    -Real.log (250000000000 / 678112145647) ≤ (249462941 / 250000000) := by
  have h := checkLog_sound (w := (178112145647 / 1178112145647)) (n := 12)
    (lo := (152352291 / 500000000)) (hi := (304704583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678112145647 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(678112145647 / 500000000000) = 1/(250000000000 / 678112145647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (498925881 / 500000000) (249462941 / 250000000) (Real.log (678112145647 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (678112145647 / 250000000000) = -Real.log (250000000000 / 678112145647) := by
    rw [show ((678112145647 / 250000000000) : ℝ) = ((250000000000 / 678112145647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (721271733 / 1000000000) ≤ -Real.log (500000000000 / 1028523782301) ∧
    -Real.log (500000000000 / 1028523782301) ≤ (144254347 / 200000000) := by
  have h := checkLog_sound (w := (28523782301 / 2028523782301)) (n := 12)
    (lo := (28124553 / 1000000000)) (hi := (14062277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1028523782301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1028523782301 / 1000000000000) = 1/(500000000000 / 1028523782301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (721271733 / 1000000000) (144254347 / 200000000) (Real.log (1028523782301 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1028523782301 / 500000000000) = -Real.log (500000000000 / 1028523782301) := by
    rw [show ((1028523782301 / 500000000000) : ℝ) = ((500000000000 / 1028523782301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (722978201 / 1000000000) ≤ -Real.log (31250000000 / 64392526493) ∧
    -Real.log (31250000000 / 64392526493) ≤ (722978203 / 1000000000) := by
  have h := checkLog_sound (w := (1892526493 / 126892526493)) (n := 12)
    (lo := (29831021 / 1000000000)) (hi := (14915511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64392526493 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64392526493 / 62500000000) = 1/(31250000000 / 64392526493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (722978201 / 1000000000) (722978203 / 1000000000) (Real.log (64392526493 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (64392526493 / 31250000000) = -Real.log (31250000000 / 64392526493) := by
    rw [show ((64392526493 / 31250000000) : ℝ) = ((31250000000 / 64392526493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0174

import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0013
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

theorem reflection_log_1_neg : (201950693 / 500000000) ≤ -Real.log (1280 / 1917) ∧
    -Real.log (1280 / 1917) ≤ (403901387 / 1000000000) := by
  have h := checkLog_sound (w := (637 / 3197)) (n := 12)
    (lo := (201950693 / 500000000)) (hi := (403901387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1917 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1917 / 1280) = 1/(1280 / 1917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (201950693 / 500000000) (403901387 / 1000000000) (Real.log (1917 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1917 / 1280) = -Real.log (1280 / 1917) := by
    rw [show ((1917 / 1280) : ℝ) = ((1280 / 1917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (86058829 / 125000000) ≤ -Real.log (643 / 1280) ∧
    -Real.log (643 / 1280) ≤ (688470633 / 1000000000) := by
  have h := checkLog_sound (w := (637 / 1923)) (n := 12)
    (lo := (86058829 / 125000000)) (hi := (688470633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 643) = 1/(643 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-688470633 / 1000000000) (-86058829 / 125000000) (Real.log (643 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (403118607 / 1000000000) ≤ -Real.log (2560 / 3831) ∧
    -Real.log (2560 / 3831) ≤ (25194913 / 62500000) := by
  have h := checkLog_sound (w := (1271 / 6391)) (n := 12)
    (lo := (403118607 / 1000000000)) (hi := (25194913 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3831 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3831 / 2560) = 1/(2560 / 3831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (403118607 / 1000000000) (25194913 / 62500000) (Real.log (3831 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3831 / 2560) = -Real.log (2560 / 3831) := by
    rw [show ((3831 / 2560) : ℝ) = ((2560 / 3831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (343070267 / 500000000) ≤ -Real.log (1289 / 2560) ∧
    -Real.log (1289 / 2560) ≤ (137228107 / 200000000) := by
  have h := checkLog_sound (w := (1271 / 3849)) (n := 12)
    (lo := (343070267 / 500000000)) (hi := (137228107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1289) = 1/(1289 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-137228107 / 200000000) (-343070267 / 500000000) (Real.log (1289 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (690800679 / 1000000000) ≤ -Real.log (640 / 1277) ∧
    -Real.log (640 / 1277) ≤ (17270017 / 25000000) := by
  have h := checkLog_sound (w := (637 / 1917)) (n := 12)
    (lo := (690800679 / 1000000000)) (hi := (17270017 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1277 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1277 / 640) = 1/(640 / 1277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (690800679 / 1000000000) (17270017 / 25000000) (Real.log (1277 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1277 / 640) = -Real.log (640 / 1277) := by
    rw [show ((1277 / 640) : ℝ) = ((640 / 1277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (5362855883 / 1000000000) ≤ -Real.log (3 / 640) ∧
    -Real.log (3 / 640) ≤ (5362855891 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(5 / 3) = 1/(3 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5362855891 / 1000000000) (-5362855883 / 1000000000) (Real.log (3 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (689625361 / 1000000000) ≤ -Real.log (1280 / 2551) ∧
    -Real.log (1280 / 2551) ≤ (344812681 / 500000000) := by
  have h := checkLog_sound (w := (1271 / 3831)) (n := 12)
    (lo := (689625361 / 1000000000)) (hi := (344812681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2551 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2551 / 1280) = 1/(1280 / 2551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (689625361 / 1000000000) (344812681 / 500000000) (Real.log (2551 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2551 / 1280) = -Real.log (1280 / 2551) := by
    rw [show ((2551 / 1280) : ℝ) = ((1280 / 2551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (198295631 / 40000000) ≤ -Real.log (9 / 1280) ∧
    -Real.log (9 / 1280) ≤ (4957390783 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(10 / 9) = 1/(9 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-4957390783 / 1000000000) (-198295631 / 40000000) (Real.log (9 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (142548199 / 250000000) ≤ -Real.log (31250 / 55269) ∧
    -Real.log (31250 / 55269) ≤ (570192797 / 1000000000) := by
  have h := checkLog_sound (w := (24019 / 86519)) (n := 12)
    (lo := (142548199 / 250000000)) (hi := (570192797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55269 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55269 / 31250) = 1/(31250 / 55269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (142548199 / 250000000) (570192797 / 1000000000) (Real.log (55269 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (55269 / 31250) = -Real.log (31250 / 55269) := by
    rw [show ((55269 / 31250) : ℝ) = ((31250 / 55269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (292728407 / 200000000) ≤ -Real.log (7231 / 31250) ∧
    -Real.log (7231 / 31250) ≤ (731821019 / 500000000) := by
  have h := checkLog_sound (w := (1163 / 30087)) (n := 12)
    (lo := (3093907 / 40000000)) (hi := (19336919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14462) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 14462) = 1/(7231 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-731821019 / 500000000) (-292728407 / 200000000) (Real.log (7231 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (572085149 / 1000000000) ≤ -Real.log (500000 / 885979) ∧
    -Real.log (500000 / 885979) ≤ (11441703 / 20000000) := by
  have h := checkLog_sound (w := (385979 / 1385979)) (n := 12)
    (lo := (572085149 / 1000000000)) (hi := (11441703 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885979 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885979 / 500000) = 1/(500000 / 885979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (572085149 / 1000000000) (11441703 / 20000000) (Real.log (885979 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (885979 / 500000) = -Real.log (500000 / 885979) := by
    rw [show ((885979 / 500000) : ℝ) = ((500000 / 885979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (295645091 / 200000000) ≤ -Real.log (114021 / 500000) ∧
    -Real.log (114021 / 500000) ≤ (739112729 / 500000000) := by
  have h := checkLog_sound (w := (10979 / 239021)) (n := 12)
    (lo := (18386219 / 200000000)) (hi := (11491387 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114021) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 114021) = 1/(114021 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-739112729 / 500000000) (-295645091 / 200000000) (Real.log (114021 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (49861781 / 100000000) ≤ -Real.log (250000 / 411611) ∧
    -Real.log (250000 / 411611) ≤ (498617811 / 1000000000) := by
  have h := checkLog_sound (w := (161611 / 661611)) (n := 12)
    (lo := (49861781 / 100000000)) (hi := (498617811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411611 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411611 / 250000) = 1/(250000 / 411611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (49861781 / 100000000) (498617811 / 1000000000) (Real.log (411611 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (411611 / 250000) = -Real.log (250000 / 411611) := by
    rw [show ((411611 / 250000) : ℝ) = ((250000 / 411611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1039713389 / 1000000000) ≤ -Real.log (88389 / 250000) ∧
    -Real.log (88389 / 250000) ≤ (1039713391 / 1000000000) := by
  have h := checkLog_sound (w := (36611 / 213389)) (n := 12)
    (lo := (346566209 / 1000000000)) (hi := (34656621 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88389) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 88389) = 1/(88389 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1039713391 / 1000000000) (-1039713389 / 1000000000) (Real.log (88389 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (125220487 / 250000000) ≤ -Real.log (15625 / 25784) ∧
    -Real.log (15625 / 25784) ≤ (500881949 / 1000000000) := by
  have h := checkLog_sound (w := (10159 / 41409)) (n := 12)
    (lo := (125220487 / 250000000)) (hi := (500881949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25784 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25784 / 15625) = 1/(15625 / 25784) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (125220487 / 250000000) (500881949 / 1000000000) (Real.log (25784 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (25784 / 15625) = -Real.log (15625 / 25784) := by
    rw [show ((25784 / 15625) : ℝ) = ((15625 / 25784) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1050325107 / 1000000000) ≤ -Real.log (5466 / 15625) ∧
    -Real.log (5466 / 15625) ≤ (1050325109 / 1000000000) := by
  have h := checkLog_sound (w := (4693 / 26557)) (n := 12)
    (lo := (357177927 / 1000000000)) (hi := (44647241 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10932) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 10932) = 1/(5466 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1050325109 / 1000000000) (-1050325107 / 1000000000) (Real.log (5466 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (127114677 / 62500000) ≤ -Real.log (500000000000 / 3821670584981) ∧
    -Real.log (500000000000 / 3821670584981) ≤ (406766967 / 200000000) := by
  have h := checkLog_sound (w := (1821670584981 / 5821670584981)) (n := 12)
    (lo := (80942559 / 125000000)) (hi := (647540473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3821670584981 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3821670584981 / 2000000000000) = 1/(500000000000 / 3821670584981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (127114677 / 62500000) (406766967 / 200000000) (Real.log (3821670584981 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3821670584981 / 500000000000) = -Real.log (500000000000 / 3821670584981) := by
    rw [show ((3821670584981 / 500000000000) : ℝ) = ((500000000000 / 3821670584981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (410062121 / 200000000) ≤ -Real.log (25000000000 / 194257856009) ∧
    -Real.log (25000000000 / 194257856009) ≤ (128144413 / 62500000) := by
  have h := checkLog_sound (w := (94257856009 / 294257856009)) (n := 12)
    (lo := (132803249 / 200000000)) (hi := (332008123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194257856009 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(194257856009 / 100000000000) = 1/(25000000000 / 194257856009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (410062121 / 200000000) (128144413 / 62500000) (Real.log (194257856009 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (194257856009 / 25000000000) = -Real.log (25000000000 / 194257856009) := by
    rw [show ((194257856009 / 25000000000) : ℝ) = ((25000000000 / 194257856009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1538331199 / 1000000000) ≤ -Real.log (250000000000 / 1164203124823) ∧
    -Real.log (250000000000 / 1164203124823) ≤ (769165601 / 500000000) := by
  have h := checkLog_sound (w := (164203124823 / 2164203124823)) (n := 12)
    (lo := (152036839 / 1000000000)) (hi := (3800921 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164203124823 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1164203124823 / 1000000000000) = 1/(250000000000 / 1164203124823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1538331199 / 1000000000) (769165601 / 500000000) (Real.log (1164203124823 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1164203124823 / 250000000000) = -Real.log (250000000000 / 1164203124823) := by
    rw [show ((1164203124823 / 250000000000) : ℝ) = ((250000000000 / 1164203124823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (310241411 / 200000000) ≤ -Real.log (500000000000 / 2358580314673) ∧
    -Real.log (500000000000 / 2358580314673) ≤ (775603529 / 500000000) := by
  have h := checkLog_sound (w := (358580314673 / 4358580314673)) (n := 12)
    (lo := (32982539 / 200000000)) (hi := (20614087 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2358580314673 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2358580314673 / 2000000000000) = 1/(500000000000 / 2358580314673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (310241411 / 200000000) (775603529 / 500000000) (Real.log (2358580314673 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2358580314673 / 500000000000) = -Real.log (500000000000 / 2358580314673) := by
    rw [show ((2358580314673 / 500000000000) : ℝ) = ((500000000000 / 2358580314673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0013

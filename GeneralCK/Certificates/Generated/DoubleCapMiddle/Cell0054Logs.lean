import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0054
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

theorem reflection_log_1_neg : (371294123 / 1000000000) ≤ -Real.log (2560 / 3711) ∧
    -Real.log (2560 / 3711) ≤ (92823531 / 250000000) := by
  have h := checkLog_sound (w := (1151 / 6271)) (n := 12)
    (lo := (371294123 / 1000000000)) (hi := (92823531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3711 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3711 / 2560) = 1/(2560 / 3711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (371294123 / 1000000000) (92823531 / 250000000) (Real.log (3711 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3711 / 2560) = -Real.log (2560 / 3711) := by
    rw [show ((3711 / 2560) : ℝ) = ((2560 / 3711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (23885081 / 40000000) ≤ -Real.log (1409 / 2560) ∧
    -Real.log (1409 / 2560) ≤ (298563513 / 500000000) := by
  have h := checkLog_sound (w := (1151 / 3969)) (n := 12)
    (lo := (23885081 / 40000000)) (hi := (298563513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1409) = 1/(1409 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-298563513 / 500000000) (-23885081 / 40000000) (Real.log (1409 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (370485389 / 1000000000) ≤ -Real.log (640 / 927) ∧
    -Real.log (640 / 927) ≤ (37048539 / 100000000) := by
  have h := checkLog_sound (w := (287 / 1567)) (n := 12)
    (lo := (370485389 / 1000000000)) (hi := (37048539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927 / 640) = 1/(640 / 927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (370485389 / 1000000000) (37048539 / 100000000) (Real.log (927 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (927 / 640) = -Real.log (640 / 927) := by
    rw [show ((927 / 640) : ℝ) = ((640 / 927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (595000119 / 1000000000) ≤ -Real.log (353 / 640) ∧
    -Real.log (353 / 640) ≤ (14875003 / 25000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 353) = 1/(353 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-14875003 / 25000000) (-595000119 / 1000000000) (Real.log (353 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (641442617 / 1000000000) ≤ -Real.log (1280 / 2431) ∧
    -Real.log (1280 / 2431) ≤ (320721309 / 500000000) := by
  have h := checkLog_sound (w := (1151 / 3711)) (n := 12)
    (lo := (641442617 / 1000000000)) (hi := (320721309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2431 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2431 / 1280) = 1/(1280 / 2431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (641442617 / 1000000000) (320721309 / 500000000) (Real.log (2431 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2431 / 1280) = -Real.log (1280 / 2431) := by
    rw [show ((2431 / 1280) : ℝ) = ((1280 / 2431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (45896059 / 20000000) ≤ -Real.log (129 / 1280) ∧
    -Real.log (129 / 1280) ≤ (1147401477 / 500000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 129) = 1/(129 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1147401477 / 500000000) (-45896059 / 20000000) (Real.log (129 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (128041559 / 200000000) ≤ -Real.log (320 / 607) ∧
    -Real.log (320 / 607) ≤ (160051949 / 250000000) := by
  have h := checkLog_sound (w := (287 / 927)) (n := 12)
    (lo := (128041559 / 200000000)) (hi := (160051949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607 / 320) = 1/(320 / 607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (128041559 / 200000000) (160051949 / 250000000) (Real.log (607 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (607 / 320) = -Real.log (320 / 607) := by
    rw [show ((607 / 320) : ℝ) = ((320 / 607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (283976679 / 125000000) ≤ -Real.log (33 / 320) ∧
    -Real.log (33 / 320) ≤ (567953359 / 250000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 33) = 1/(33 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-567953359 / 250000000) (-283976679 / 125000000) (Real.log (33 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (512638579 / 1000000000) ≤ -Real.log (1000000 / 1669691) ∧
    -Real.log (1000000 / 1669691) ≤ (25631929 / 50000000) := by
  have h := checkLog_sound (w := (669691 / 2669691)) (n := 12)
    (lo := (512638579 / 1000000000)) (hi := (25631929 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1669691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1669691 / 1000000) = 1/(1000000 / 1669691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (512638579 / 1000000000) (25631929 / 50000000) (Real.log (1669691 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1669691 / 1000000) = -Real.log (1000000 / 1669691) := by
    rw [show ((1669691 / 1000000) : ℝ) = ((1000000 / 1669691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (553863349 / 500000000) ≤ -Real.log (330309 / 1000000) ∧
    -Real.log (330309 / 1000000) ≤ (11077267 / 10000000) := by
  have h := checkLog_sound (w := (169691 / 830309)) (n := 12)
    (lo := (207289759 / 500000000)) (hi := (414579519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 330309) = 1/(330309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-11077267 / 10000000) (-553863349 / 500000000) (Real.log (330309 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (256951043 / 500000000) ≤ -Real.log (500000 / 835901) ∧
    -Real.log (500000 / 835901) ≤ (513902087 / 1000000000) := by
  have h := checkLog_sound (w := (335901 / 1335901)) (n := 12)
    (lo := (256951043 / 500000000)) (hi := (513902087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835901 / 500000) = 1/(500000 / 835901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (256951043 / 500000000) (513902087 / 1000000000) (Real.log (835901 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (835901 / 500000) = -Real.log (500000 / 835901) := by
    rw [show ((835901 / 500000) : ℝ) = ((500000 / 835901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1114138193 / 1000000000) ≤ -Real.log (164099 / 500000) ∧
    -Real.log (164099 / 500000) ≤ (222827639 / 200000000) := by
  have h := checkLog_sound (w := (85901 / 414099)) (n := 12)
    (lo := (420991013 / 1000000000)) (hi := (210495507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164099) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 164099) = 1/(164099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-222827639 / 200000000) (-1114138193 / 1000000000) (Real.log (164099 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (86328819 / 200000000) ≤ -Real.log (1000000 / 1539787) ∧
    -Real.log (1000000 / 1539787) ≤ (6744439 / 15625000) := by
  have h := checkLog_sound (w := (539787 / 2539787)) (n := 12)
    (lo := (86328819 / 200000000)) (hi := (6744439 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1539787 / 1000000) = 1/(1000000 / 1539787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (86328819 / 200000000) (6744439 / 15625000) (Real.log (1539787 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1539787 / 1000000) = -Real.log (1000000 / 1539787) := by
    rw [show ((1539787 / 1000000) : ℝ) = ((1000000 / 1539787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (194016463 / 250000000) ≤ -Real.log (460213 / 1000000) ∧
    -Real.log (460213 / 1000000) ≤ (388032927 / 500000000) := by
  have h := checkLog_sound (w := (39787 / 960213)) (n := 12)
    (lo := (5182417 / 62500000)) (hi := (82918673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 460213) = 1/(460213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-388032927 / 500000000) (-194016463 / 250000000) (Real.log (460213 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (433051091 / 1000000000) ≤ -Real.log (200000 / 308391) ∧
    -Real.log (200000 / 308391) ≤ (108262773 / 250000000) := by
  have h := checkLog_sound (w := (108391 / 508391)) (n := 12)
    (lo := (433051091 / 1000000000)) (hi := (108262773 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308391 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308391 / 200000) = 1/(200000 / 308391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (433051091 / 1000000000) (108262773 / 250000000) (Real.log (308391 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (308391 / 200000) = -Real.log (200000 / 308391) := by
    rw [show ((308391 / 200000) : ℝ) = ((200000 / 308391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (156157569 / 200000000) ≤ -Real.log (91609 / 200000) ∧
    -Real.log (91609 / 200000) ≤ (780787847 / 1000000000) := by
  have h := checkLog_sound (w := (8391 / 191609)) (n := 12)
    (lo := (17528133 / 200000000)) (hi := (43820333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 91609) = 1/(91609 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-780787847 / 1000000000) (-156157569 / 200000000) (Real.log (91609 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1620365277 / 1000000000) ≤ -Real.log (31250000000 / 157966763697) ∧
    -Real.log (31250000000 / 157966763697) ≤ (10127283 / 6250000) := by
  have h := checkLog_sound (w := (32966763697 / 282966763697)) (n := 12)
    (lo := (234070917 / 1000000000)) (hi := (117035459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157966763697 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(157966763697 / 125000000000) = 1/(31250000000 / 157966763697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1620365277 / 1000000000) (10127283 / 6250000) (Real.log (157966763697 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (157966763697 / 31250000000) = -Real.log (31250000000 / 157966763697) := by
    rw [show ((157966763697 / 31250000000) : ℝ) = ((31250000000 / 157966763697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1628040279 / 1000000000) ≤ -Real.log (250000000000 / 1273470587877) ∧
    -Real.log (250000000000 / 1273470587877) ≤ (814020141 / 500000000) := by
  have h := checkLog_sound (w := (273470587877 / 2273470587877)) (n := 12)
    (lo := (241745919 / 1000000000)) (hi := (94432 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273470587877 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1273470587877 / 1000000000000) = 1/(250000000000 / 1273470587877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1628040279 / 1000000000) (814020141 / 500000000) (Real.log (1273470587877 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1273470587877 / 250000000000) = -Real.log (250000000000 / 1273470587877) := by
    rw [show ((1273470587877 / 250000000000) : ℝ) = ((250000000000 / 1273470587877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1207709947 / 1000000000) ≤ -Real.log (62500000000 / 209113361639) ∧
    -Real.log (62500000000 / 209113361639) ≤ (1207709949 / 1000000000) := by
  have h := checkLog_sound (w := (84113361639 / 334113361639)) (n := 12)
    (lo := (514562767 / 1000000000)) (hi := (32160173 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209113361639 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(209113361639 / 125000000000) = 1/(62500000000 / 209113361639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1207709947 / 1000000000) (1207709949 / 1000000000) (Real.log (209113361639 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (209113361639 / 62500000000) = -Real.log (62500000000 / 209113361639) := by
    rw [show ((209113361639 / 62500000000) : ℝ) = ((62500000000 / 209113361639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1213838937 / 1000000000) ≤ -Real.log (125000000000 / 420797901953) ∧
    -Real.log (125000000000 / 420797901953) ≤ (1213838939 / 1000000000) := by
  have h := checkLog_sound (w := (170797901953 / 670797901953)) (n := 12)
    (lo := (520691757 / 1000000000)) (hi := (260345879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((420797901953 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(420797901953 / 250000000000) = 1/(125000000000 / 420797901953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1213838937 / 1000000000) (1213838939 / 1000000000) (Real.log (420797901953 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (420797901953 / 125000000000) = -Real.log (125000000000 / 420797901953) := by
    rw [show ((420797901953 / 125000000000) : ℝ) = ((125000000000 / 420797901953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0054

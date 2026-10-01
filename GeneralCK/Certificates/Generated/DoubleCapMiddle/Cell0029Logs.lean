import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0029
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

theorem reflection_log_1_neg : (195651397 / 500000000) ≤ -Real.log (1280 / 1893) ∧
    -Real.log (1280 / 1893) ≤ (78260559 / 200000000) := by
  have h := checkLog_sound (w := (613 / 3173)) (n := 12)
    (lo := (195651397 / 500000000)) (hi := (78260559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1893 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1893 / 1280) = 1/(1280 / 1893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (195651397 / 500000000) (78260559 / 200000000) (Real.log (1893 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1893 / 1280) = -Real.log (1280 / 1893) := by
    rw [show ((1893 / 1280) : ℝ) = ((1280 / 1893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (65182531 / 100000000) ≤ -Real.log (667 / 1280) ∧
    -Real.log (667 / 1280) ≤ (651825311 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 1947)) (n := 12)
    (lo := (65182531 / 100000000)) (hi := (651825311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 667) = 1/(667 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-651825311 / 1000000000) (-65182531 / 100000000) (Real.log (667 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (390510087 / 1000000000) ≤ -Real.log (2560 / 3783) ∧
    -Real.log (2560 / 3783) ≤ (48813761 / 125000000) := by
  have h := checkLog_sound (w := (1223 / 6343)) (n := 12)
    (lo := (390510087 / 1000000000)) (hi := (48813761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3783 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3783 / 2560) = 1/(2560 / 3783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (390510087 / 1000000000) (48813761 / 125000000) (Real.log (3783 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3783 / 2560) = -Real.log (2560 / 3783) := by
    rw [show ((3783 / 2560) : ℝ) = ((2560 / 3783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (8119737 / 12500000) ≤ -Real.log (1337 / 2560) ∧
    -Real.log (1337 / 2560) ≤ (649578961 / 1000000000) := by
  have h := checkLog_sound (w := (1223 / 3897)) (n := 12)
    (lo := (8119737 / 12500000)) (hi := (649578961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1337) = 1/(1337 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-649578961 / 1000000000) (-8119737 / 12500000) (Real.log (1337 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (335913889 / 500000000) ≤ -Real.log (640 / 1253) ∧
    -Real.log (640 / 1253) ≤ (671827779 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 1893)) (n := 12)
    (lo := (335913889 / 500000000)) (hi := (671827779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253 / 640) = 1/(640 / 1253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (335913889 / 500000000) (671827779 / 1000000000) (Real.log (1253 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1253 / 640) = -Real.log (640 / 1253) := by
    rw [show ((1253 / 640) : ℝ) = ((640 / 1253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (791407827 / 250000000) ≤ -Real.log (27 / 640) ∧
    -Real.log (27 / 640) ≤ (3165631313 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 27) = 1/(27 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3165631313 / 1000000000) (-791407827 / 250000000) (Real.log (27 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (335314967 / 500000000) ≤ -Real.log (1280 / 2503) ∧
    -Real.log (1280 / 2503) ≤ (134125987 / 200000000) := by
  have h := checkLog_sound (w := (1223 / 3783)) (n := 12)
    (lo := (335314967 / 500000000)) (hi := (134125987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2503 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2503 / 1280) = 1/(1280 / 2503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (335314967 / 500000000) (134125987 / 200000000) (Real.log (2503 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2503 / 1280) = -Real.log (1280 / 2503) := by
    rw [show ((2503 / 1280) : ℝ) = ((1280 / 2503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1555782043 / 500000000) ≤ -Real.log (57 / 1280) ∧
    -Real.log (57 / 1280) ≤ (3111564091 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 57) = 1/(57 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3111564091 / 1000000000) (-1555782043 / 500000000) (Real.log (57 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (545517443 / 1000000000) ≤ -Real.log (1000000 / 1725501) ∧
    -Real.log (1000000 / 1725501) ≤ (136379361 / 250000000) := by
  have h := checkLog_sound (w := (725501 / 2725501)) (n := 12)
    (lo := (545517443 / 1000000000)) (hi := (136379361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1725501 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1725501 / 1000000) = 1/(1000000 / 1725501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (545517443 / 1000000000) (136379361 / 250000000) (Real.log (1725501 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1725501 / 1000000) = -Real.log (1000000 / 1725501) := by
    rw [show ((1725501 / 1000000) : ℝ) = ((1000000 / 1725501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (64640383 / 50000000) ≤ -Real.log (274499 / 1000000) ∧
    -Real.log (274499 / 1000000) ≤ (646403831 / 500000000) := by
  have h := checkLog_sound (w := (225501 / 774499)) (n := 12)
    (lo := (1873939 / 3125000)) (hi := (599660481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 274499) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 274499) = 1/(274499 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-646403831 / 500000000) (-64640383 / 50000000) (Real.log (274499 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (546920687 / 1000000000) ≤ -Real.log (250000 / 431981) ∧
    -Real.log (250000 / 431981) ≤ (34182543 / 62500000) := by
  have h := checkLog_sound (w := (181981 / 681981)) (n := 12)
    (lo := (546920687 / 1000000000)) (hi := (34182543 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431981 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431981 / 250000) = 1/(250000 / 431981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (546920687 / 1000000000) (34182543 / 62500000) (Real.log (431981 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (431981 / 250000) = -Real.log (250000 / 431981) := by
    rw [show ((431981 / 250000) : ℝ) = ((250000 / 431981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1301673839 / 1000000000) ≤ -Real.log (68019 / 250000) ∧
    -Real.log (68019 / 250000) ≤ (1301673841 / 1000000000) := by
  have h := checkLog_sound (w := (56981 / 193019)) (n := 12)
    (lo := (608526659 / 1000000000)) (hi := (30426333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 68019) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 68019) = 1/(68019 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1301673841 / 1000000000) (-1301673839 / 1000000000) (Real.log (68019 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (93846041 / 200000000) ≤ -Real.log (1000000 / 1598763) ∧
    -Real.log (1000000 / 1598763) ≤ (234615103 / 500000000) := by
  have h := checkLog_sound (w := (598763 / 2598763)) (n := 12)
    (lo := (93846041 / 200000000)) (hi := (234615103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1598763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1598763 / 1000000) = 1/(1000000 / 1598763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (93846041 / 200000000) (234615103 / 500000000) (Real.log (1598763 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1598763 / 1000000) = -Real.log (1000000 / 1598763) := by
    rw [show ((1598763 / 1000000) : ℝ) = ((1000000 / 1598763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (913203003 / 1000000000) ≤ -Real.log (401237 / 1000000) ∧
    -Real.log (401237 / 1000000) ≤ (182640601 / 200000000) := by
  have h := checkLog_sound (w := (98763 / 901237)) (n := 12)
    (lo := (220055823 / 1000000000)) (hi := (13753489 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 401237) = 1/(401237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-182640601 / 200000000) (-913203003 / 1000000000) (Real.log (401237 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (235439123 / 500000000) ≤ -Real.log (5000 / 8007) ∧
    -Real.log (5000 / 8007) ≤ (470878247 / 1000000000) := by
  have h := checkLog_sound (w := (3007 / 13007)) (n := 12)
    (lo := (235439123 / 500000000)) (hi := (470878247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8007 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8007 / 5000) = 1/(5000 / 8007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (235439123 / 500000000) (470878247 / 1000000000) (Real.log (8007 / 5000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (8007 / 5000) = -Real.log (5000 / 8007) := by
    rw [show ((8007 / 5000) : ℝ) = ((5000 / 8007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (91979687 / 100000000) ≤ -Real.log (1993 / 5000) ∧
    -Real.log (1993 / 5000) ≤ (114974609 / 125000000) := by
  have h := checkLog_sound (w := (507 / 4493)) (n := 12)
    (lo := (22664969 / 100000000)) (hi := (226649691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2500 / 1993) = 1/(1993 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-114974609 / 125000000) (-91979687 / 100000000) (Real.log (1993 / 5000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1838325103 / 1000000000) ≤ -Real.log (500000000000 / 3143000520949) ∧
    -Real.log (500000000000 / 3143000520949) ≤ (919162553 / 500000000) := by
  have h := checkLog_sound (w := (1143000520949 / 5143000520949)) (n := 12)
    (lo := (452030743 / 1000000000)) (hi := (56503843 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3143000520949 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3143000520949 / 2000000000000) = 1/(500000000000 / 3143000520949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1838325103 / 1000000000) (919162553 / 500000000) (Real.log (3143000520949 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3143000520949 / 500000000000) = -Real.log (500000000000 / 3143000520949) := by
    rw [show ((3143000520949 / 500000000000) : ℝ) = ((500000000000 / 3143000520949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (924297263 / 500000000) ≤ -Real.log (250000000000 / 1587721813023) ∧
    -Real.log (250000000000 / 1587721813023) ≤ (1848594529 / 1000000000) := by
  have h := checkLog_sound (w := (587721813023 / 2587721813023)) (n := 12)
    (lo := (231150083 / 500000000)) (hi := (462300167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1587721813023 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1587721813023 / 1000000000000) = 1/(250000000000 / 1587721813023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (924297263 / 500000000) (1848594529 / 1000000000) (Real.log (1587721813023 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1587721813023 / 250000000000) = -Real.log (250000000000 / 1587721813023) := by
    rw [show ((1587721813023 / 250000000000) : ℝ) = ((250000000000 / 1587721813023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (172804151 / 125000000) ≤ -Real.log (25000000000 / 99614629259) ∧
    -Real.log (25000000000 / 99614629259) ≤ (138243321 / 100000000) := by
  have h := checkLog_sound (w := (49614629259 / 149614629259)) (n := 12)
    (lo := (172321507 / 250000000)) (hi := (689286029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99614629259 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(99614629259 / 50000000000) = 1/(25000000000 / 99614629259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (172804151 / 125000000) (138243321 / 100000000) (Real.log (99614629259 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (99614629259 / 25000000000) = -Real.log (25000000000 / 99614629259) := by
    rw [show ((99614629259 / 25000000000) : ℝ) = ((25000000000 / 99614629259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (347668779 / 250000000) ≤ -Real.log (125000000000 / 502195183141) ∧
    -Real.log (125000000000 / 502195183141) ≤ (1390675119 / 1000000000) := by
  have h := checkLog_sound (w := (2195183141 / 1002195183141)) (n := 12)
    (lo := (1095189 / 250000000)) (hi := (4380757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((502195183141 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(502195183141 / 500000000000) = 1/(125000000000 / 502195183141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (347668779 / 250000000) (1390675119 / 1000000000) (Real.log (502195183141 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (502195183141 / 125000000000) = -Real.log (125000000000 / 502195183141) := by
    rw [show ((502195183141 / 125000000000) : ℝ) = ((125000000000 / 502195183141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0029

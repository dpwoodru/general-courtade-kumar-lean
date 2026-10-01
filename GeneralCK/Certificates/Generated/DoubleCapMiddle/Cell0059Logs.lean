import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0059
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

theorem reflection_log_1_neg : (73448779 / 200000000) ≤ -Real.log (160 / 231) ∧
    -Real.log (160 / 231) ≤ (45905487 / 125000000) := by
  have h := checkLog_sound (w := (71 / 391)) (n := 12)
    (lo := (73448779 / 200000000)) (hi := (45905487 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231 / 160) = 1/(160 / 231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (73448779 / 200000000) (45905487 / 125000000) (Real.log (231 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (231 / 160) = -Real.log (160 / 231) := by
    rw [show ((231 / 160) : ℝ) = ((160 / 231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (117307489 / 200000000) ≤ -Real.log (89 / 160) ∧
    -Real.log (89 / 160) ≤ (293268723 / 500000000) := by
  have h := checkLog_sound (w := (71 / 249)) (n := 12)
    (lo := (117307489 / 200000000)) (hi := (293268723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 89) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 89) = 1/(89 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-293268723 / 500000000) (-117307489 / 200000000) (Real.log (89 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (366431877 / 1000000000) ≤ -Real.log (2560 / 3693) ∧
    -Real.log (2560 / 3693) ≤ (183215939 / 500000000) := by
  have h := checkLog_sound (w := (1133 / 6253)) (n := 12)
    (lo := (366431877 / 1000000000)) (hi := (183215939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3693 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3693 / 2560) = 1/(2560 / 3693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (366431877 / 1000000000) (183215939 / 500000000) (Real.log (3693 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3693 / 2560) = -Real.log (2560 / 3693) := by
    rw [show ((3693 / 2560) : ℝ) = ((2560 / 3693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (584432919 / 1000000000) ≤ -Real.log (1427 / 2560) ∧
    -Real.log (1427 / 2560) ≤ (14610823 / 25000000) := by
  have h := checkLog_sound (w := (1133 / 3987)) (n := 12)
    (lo := (584432919 / 1000000000)) (hi := (14610823 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1427) = 1/(1427 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-14610823 / 25000000) (-584432919 / 1000000000) (Real.log (1427 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (317626601 / 500000000) ≤ -Real.log (80 / 151) ∧
    -Real.log (80 / 151) ≤ (635253203 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 231)) (n := 12)
    (lo := (317626601 / 500000000)) (hi := (635253203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151 / 80) = 1/(80 / 151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (317626601 / 500000000) (635253203 / 1000000000) (Real.log (151 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (151 / 80) = -Real.log (80 / 151) := by
    rw [show ((151 / 80) : ℝ) = ((80 / 151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (436960411 / 200000000) ≤ -Real.log (9 / 80) ∧
    -Real.log (9 / 80) ≤ (2184802059 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(10 / 9) = 1/(9 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2184802059 / 1000000000) (-436960411 / 200000000) (Real.log (9 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (158502677 / 250000000) ≤ -Real.log (1280 / 2413) ∧
    -Real.log (1280 / 2413) ≤ (634010709 / 1000000000) := by
  have h := checkLog_sound (w := (1133 / 3693)) (n := 12)
    (lo := (158502677 / 250000000)) (hi := (634010709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2413 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2413 / 1280) = 1/(1280 / 2413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (158502677 / 250000000) (634010709 / 1000000000) (Real.log (2413 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2413 / 1280) = -Real.log (1280 / 2413) := by
    rw [show ((2413 / 1280) : ℝ) = ((1280 / 2413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (135261423 / 62500000) ≤ -Real.log (147 / 1280) ∧
    -Real.log (147 / 1280) ≤ (541045693 / 250000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 147) = 1/(147 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-541045693 / 250000000) (-135261423 / 62500000) (Real.log (147 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (50636509 / 100000000) ≤ -Real.log (1000000 / 1659249) ∧
    -Real.log (1000000 / 1659249) ≤ (506365091 / 1000000000) := by
  have h := checkLog_sound (w := (659249 / 2659249)) (n := 12)
    (lo := (50636509 / 100000000)) (hi := (506365091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1659249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1659249 / 1000000) = 1/(1000000 / 1659249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (50636509 / 100000000) (506365091 / 1000000000) (Real.log (1659249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1659249 / 1000000) = -Real.log (1000000 / 1659249) := by
    rw [show ((1659249 / 1000000) : ℝ) = ((1000000 / 1659249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1076603273 / 1000000000) ≤ -Real.log (340751 / 1000000) ∧
    -Real.log (340751 / 1000000) ≤ (43064131 / 40000000) := by
  have h := checkLog_sound (w := (159249 / 840751)) (n := 12)
    (lo := (383456093 / 1000000000)) (hi := (191728047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 340751) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 340751) = 1/(340751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-43064131 / 40000000) (-1076603273 / 1000000000) (Real.log (340751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (126903869 / 250000000) ≤ -Real.log (40000 / 66453) ∧
    -Real.log (40000 / 66453) ≤ (507615477 / 1000000000) := by
  have h := checkLog_sound (w := (26453 / 106453)) (n := 12)
    (lo := (126903869 / 250000000)) (hi := (507615477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66453 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66453 / 40000) = 1/(40000 / 66453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (126903869 / 250000000) (507615477 / 1000000000) (Real.log (66453 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (66453 / 40000) = -Real.log (40000 / 66453) := by
    rw [show ((66453 / 40000) : ℝ) = ((40000 / 66453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (270678583 / 250000000) ≤ -Real.log (13547 / 40000) ∧
    -Real.log (13547 / 40000) ≤ (541357167 / 500000000) := by
  have h := checkLog_sound (w := (6453 / 33547)) (n := 12)
    (lo := (24347947 / 62500000)) (hi := (389567153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 13547) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 13547) = 1/(13547 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-541357167 / 500000000) (-270678583 / 250000000) (Real.log (13547 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (53087777 / 125000000) ≤ -Real.log (200000 / 305827) ∧
    -Real.log (200000 / 305827) ≤ (424702217 / 1000000000) := by
  have h := checkLog_sound (w := (105827 / 505827)) (n := 12)
    (lo := (53087777 / 125000000)) (hi := (424702217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305827 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305827 / 200000) = 1/(200000 / 305827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (53087777 / 125000000) (424702217 / 1000000000) (Real.log (305827 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (305827 / 200000) = -Real.log (200000 / 305827) := by
    rw [show ((305827 / 200000) : ℝ) = ((200000 / 305827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (753183849 / 1000000000) ≤ -Real.log (94173 / 200000) ∧
    -Real.log (94173 / 200000) ≤ (753183851 / 1000000000) := by
  have h := checkLog_sound (w := (5827 / 194173)) (n := 12)
    (lo := (60036669 / 1000000000)) (hi := (6003667 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 94173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 94173) = 1/(94173 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-753183851 / 1000000000) (-753183849 / 1000000000) (Real.log (94173 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (426079823 / 1000000000) ≤ -Real.log (1000000 / 1531243) ∧
    -Real.log (1000000 / 1531243) ≤ (26629989 / 62500000) := by
  have h := checkLog_sound (w := (531243 / 2531243)) (n := 12)
    (lo := (426079823 / 1000000000)) (hi := (26629989 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1531243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1531243 / 1000000) = 1/(1000000 / 1531243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (426079823 / 1000000000) (26629989 / 62500000) (Real.log (1531243 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1531243 / 1000000) = -Real.log (1000000 / 1531243) := by
    rw [show ((1531243 / 1000000) : ℝ) = ((1000000 / 1531243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (757670767 / 1000000000) ≤ -Real.log (468757 / 1000000) ∧
    -Real.log (468757 / 1000000) ≤ (757670769 / 1000000000) := by
  have h := checkLog_sound (w := (31243 / 968757)) (n := 12)
    (lo := (64523587 / 1000000000)) (hi := (16130897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 468757) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 468757) = 1/(468757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-757670769 / 1000000000) (-757670767 / 1000000000) (Real.log (468757 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (791484181 / 500000000) ≤ -Real.log (500000000000 / 2434694248879) ∧
    -Real.log (500000000000 / 2434694248879) ≤ (316593673 / 200000000) := by
  have h := checkLog_sound (w := (434694248879 / 4434694248879)) (n := 12)
    (lo := (98337001 / 500000000)) (hi := (196674003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2434694248879 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2434694248879 / 2000000000000) = 1/(500000000000 / 2434694248879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (791484181 / 500000000) (316593673 / 200000000) (Real.log (2434694248879 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2434694248879 / 500000000000) = -Real.log (500000000000 / 2434694248879) := by
    rw [show ((2434694248879 / 500000000000) : ℝ) = ((500000000000 / 2434694248879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1590329809 / 1000000000) ≤ -Real.log (100000000000 / 490536650181) ∧
    -Real.log (100000000000 / 490536650181) ≤ (397582453 / 250000000) := by
  have h := checkLog_sound (w := (90536650181 / 890536650181)) (n := 12)
    (lo := (204035449 / 1000000000)) (hi := (4080709 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490536650181 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(490536650181 / 400000000000) = 1/(100000000000 / 490536650181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1590329809 / 1000000000) (397582453 / 250000000) (Real.log (490536650181 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (490536650181 / 100000000000) = -Real.log (100000000000 / 490536650181) := by
    rw [show ((490536650181 / 100000000000) : ℝ) = ((100000000000 / 490536650181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (235577213 / 200000000) ≤ -Real.log (500000000000 / 1623750968961) ∧
    -Real.log (500000000000 / 1623750968961) ≤ (1177886067 / 1000000000) := by
  have h := checkLog_sound (w := (623750968961 / 2623750968961)) (n := 12)
    (lo := (96947777 / 200000000)) (hi := (242369443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1623750968961 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1623750968961 / 1000000000000) = 1/(500000000000 / 1623750968961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (235577213 / 200000000) (1177886067 / 1000000000) (Real.log (1623750968961 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1623750968961 / 500000000000) = -Real.log (500000000000 / 1623750968961) := by
    rw [show ((1623750968961 / 500000000000) : ℝ) = ((500000000000 / 1623750968961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1183750591 / 1000000000) ≤ -Real.log (7812500000 / 25520335563) ∧
    -Real.log (7812500000 / 25520335563) ≤ (1183750593 / 1000000000) := by
  have h := checkLog_sound (w := (9895335563 / 41145335563)) (n := 12)
    (lo := (490603411 / 1000000000)) (hi := (122650853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25520335563 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25520335563 / 15625000000) = 1/(7812500000 / 25520335563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1183750591 / 1000000000) (1183750593 / 1000000000) (Real.log (25520335563 / 7812500000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (25520335563 / 7812500000) = -Real.log (7812500000 / 25520335563) := by
    rw [show ((25520335563 / 7812500000) : ℝ) = ((7812500000 / 25520335563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0059

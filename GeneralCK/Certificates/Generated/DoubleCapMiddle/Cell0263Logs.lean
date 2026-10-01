import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0263
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

theorem reflection_log_1_neg : (59238499 / 250000000) ≤ -Real.log (5120 / 6489) ∧
    -Real.log (5120 / 6489) ≤ (236953997 / 1000000000) := by
  have h := checkLog_sound (w := (1369 / 11609)) (n := 12)
    (lo := (59238499 / 250000000)) (hi := (236953997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6489 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6489 / 5120) = 1/(5120 / 6489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (59238499 / 250000000) (236953997 / 1000000000) (Real.log (6489 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6489 / 5120) = -Real.log (5120 / 6489) := by
    rw [show ((6489 / 5120) : ℝ) = ((5120 / 6489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (311131967 / 1000000000) ≤ -Real.log (3751 / 5120) ∧
    -Real.log (3751 / 5120) ≤ (4861437 / 15625000) := by
  have h := checkLog_sound (w := (1369 / 8871)) (n := 12)
    (lo := (311131967 / 1000000000)) (hi := (4861437 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3751) = 1/(3751 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4861437 / 15625000) (-311131967 / 1000000000) (Real.log (3751 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (14780723 / 62500000) ≤ -Real.log (2560 / 3243) ∧
    -Real.log (2560 / 3243) ≤ (236491569 / 1000000000) := by
  have h := checkLog_sound (w := (683 / 5803)) (n := 12)
    (lo := (14780723 / 62500000)) (hi := (236491569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3243 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3243 / 2560) = 1/(2560 / 3243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (14780723 / 62500000) (236491569 / 1000000000) (Real.log (3243 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3243 / 2560) = -Real.log (2560 / 3243) := by
    rw [show ((3243 / 2560) : ℝ) = ((2560 / 3243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (124133 / 400000) ≤ -Real.log (1877 / 2560) ∧
    -Real.log (1877 / 2560) ≤ (310332501 / 1000000000) := by
  have h := checkLog_sound (w := (683 / 4437)) (n := 12)
    (lo := (124133 / 400000)) (hi := (310332501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1877) = 1/(1877 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-310332501 / 1000000000) (-124133 / 400000) (Real.log (1877 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (214188841 / 500000000) ≤ -Real.log (2560 / 3929) ∧
    -Real.log (2560 / 3929) ≤ (428377683 / 1000000000) := by
  have h := checkLog_sound (w := (1369 / 6489)) (n := 12)
    (lo := (214188841 / 500000000)) (hi := (428377683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3929 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3929 / 2560) = 1/(2560 / 3929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (214188841 / 500000000) (428377683 / 1000000000) (Real.log (3929 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3929 / 2560) = -Real.log (2560 / 3929) := by
    rw [show ((3929 / 2560) : ℝ) = ((2560 / 3929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (765213967 / 1000000000) ≤ -Real.log (1191 / 2560) ∧
    -Real.log (1191 / 2560) ≤ (765213969 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 2471)) (n := 12)
    (lo := (72066787 / 1000000000)) (hi := (18016697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1191) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1191) = 1/(1191 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-765213969 / 1000000000) (-765213967 / 1000000000) (Real.log (1191 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (427613837 / 1000000000) ≤ -Real.log (1280 / 1963) ∧
    -Real.log (1280 / 1963) ≤ (213806919 / 500000000) := by
  have h := checkLog_sound (w := (683 / 3243)) (n := 12)
    (lo := (427613837 / 1000000000)) (hi := (213806919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963 / 1280) = 1/(1280 / 1963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (427613837 / 1000000000) (213806919 / 500000000) (Real.log (1963 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1963 / 1280) = -Real.log (1280 / 1963) := by
    rw [show ((1963 / 1280) : ℝ) = ((1280 / 1963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (381349121 / 500000000) ≤ -Real.log (597 / 1280) ∧
    -Real.log (597 / 1280) ≤ (190674561 / 250000000) := by
  have h := checkLog_sound (w := (43 / 1237)) (n := 12)
    (lo := (34775531 / 500000000)) (hi := (69551063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 597) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 597) = 1/(597 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-190674561 / 250000000) (-381349121 / 500000000) (Real.log (597 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (80957269 / 250000000) ≤ -Real.log (1000000 / 1382411) ∧
    -Real.log (1000000 / 1382411) ≤ (323829077 / 1000000000) := by
  have h := checkLog_sound (w := (382411 / 2382411)) (n := 12)
    (lo := (80957269 / 250000000)) (hi := (323829077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1382411 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1382411 / 1000000) = 1/(1000000 / 1382411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (80957269 / 250000000) (323829077 / 1000000000) (Real.log (1382411 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1382411 / 1000000) = -Real.log (1000000 / 1382411) := by
    rw [show ((1382411 / 1000000) : ℝ) = ((1000000 / 1382411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (481932091 / 1000000000) ≤ -Real.log (617589 / 1000000) ∧
    -Real.log (617589 / 1000000) ≤ (120483023 / 250000000) := by
  have h := checkLog_sound (w := (382411 / 1617589)) (n := 12)
    (lo := (481932091 / 1000000000)) (hi := (120483023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 617589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 617589) = 1/(617589 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-120483023 / 250000000) (-481932091 / 1000000000) (Real.log (617589 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (81114011 / 250000000) ≤ -Real.log (500000 / 691639) ∧
    -Real.log (500000 / 691639) ≤ (64891209 / 200000000) := by
  have h := checkLog_sound (w := (191639 / 1191639)) (n := 12)
    (lo := (81114011 / 250000000)) (hi := (64891209 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691639 / 500000) = 1/(500000 / 691639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (81114011 / 250000000) (64891209 / 200000000) (Real.log (691639 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (691639 / 500000) = -Real.log (500000 / 691639) := by
    rw [show ((691639 / 500000) : ℝ) = ((500000 / 691639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (483336923 / 1000000000) ≤ -Real.log (308361 / 500000) ∧
    -Real.log (308361 / 500000) ≤ (120834231 / 250000000) := by
  have h := checkLog_sound (w := (191639 / 808361)) (n := 12)
    (lo := (483336923 / 1000000000)) (hi := (120834231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 308361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 308361) = 1/(308361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-120834231 / 250000000) (-483336923 / 1000000000) (Real.log (308361 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2482669 / 10000000) ≤ -Real.log (500000 / 640901) ∧
    -Real.log (500000 / 640901) ≤ (248266901 / 1000000000) := by
  have h := checkLog_sound (w := (140901 / 1140901)) (n := 12)
    (lo := (2482669 / 10000000)) (hi := (248266901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640901 / 500000) = 1/(500000 / 640901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2482669 / 10000000) (248266901 / 1000000000) (Real.log (640901 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (640901 / 500000) = -Real.log (500000 / 640901) := by
    rw [show ((640901 / 500000) : ℝ) = ((500000 / 640901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (331009981 / 1000000000) ≤ -Real.log (359099 / 500000) ∧
    -Real.log (359099 / 500000) ≤ (165504991 / 500000000) := by
  have h := checkLog_sound (w := (140901 / 859099)) (n := 12)
    (lo := (331009981 / 1000000000)) (hi := (165504991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 359099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 359099) = 1/(359099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-165504991 / 500000000) (-331009981 / 1000000000) (Real.log (359099 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (248806619 / 1000000000) ≤ -Real.log (500000 / 641247) ∧
    -Real.log (500000 / 641247) ≤ (12440331 / 50000000) := by
  have h := checkLog_sound (w := (141247 / 1141247)) (n := 12)
    (lo := (248806619 / 1000000000)) (hi := (12440331 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641247 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641247 / 500000) = 1/(500000 / 641247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (248806619 / 1000000000) (12440331 / 50000000) (Real.log (641247 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (641247 / 500000) = -Real.log (500000 / 641247) := by
    rw [show ((641247 / 500000) : ℝ) = ((500000 / 641247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (331973969 / 1000000000) ≤ -Real.log (358753 / 500000) ∧
    -Real.log (358753 / 500000) ≤ (33197397 / 100000000) := by
  have h := checkLog_sound (w := (141247 / 858753)) (n := 12)
    (lo := (331973969 / 1000000000)) (hi := (33197397 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 358753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 358753) = 1/(358753 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-33197397 / 100000000) (-331973969 / 1000000000) (Real.log (358753 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (402880583 / 500000000) ≤ -Real.log (500000000000 / 1119199823831) ∧
    -Real.log (500000000000 / 1119199823831) ≤ (50360073 / 62500000) := by
  have h := checkLog_sound (w := (119199823831 / 2119199823831)) (n := 12)
    (lo := (56306993 / 500000000)) (hi := (112613987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1119199823831 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1119199823831 / 1000000000000) = 1/(500000000000 / 1119199823831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (402880583 / 500000000) (50360073 / 62500000) (Real.log (1119199823831 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1119199823831 / 500000000000) = -Real.log (500000000000 / 1119199823831) := by
    rw [show ((1119199823831 / 500000000000) : ℝ) = ((500000000000 / 1119199823831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (100974121 / 125000000) ≤ -Real.log (500000000000 / 1121476127007) ∧
    -Real.log (500000000000 / 1121476127007) ≤ (80779297 / 100000000) := by
  have h := checkLog_sound (w := (121476127007 / 2121476127007)) (n := 12)
    (lo := (28661447 / 250000000)) (hi := (114645789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121476127007 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1121476127007 / 1000000000000) = 1/(500000000000 / 1121476127007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (100974121 / 125000000) (80779297 / 100000000) (Real.log (1121476127007 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1121476127007 / 500000000000) = -Real.log (500000000000 / 1121476127007) := by
    rw [show ((1121476127007 / 500000000000) : ℝ) = ((500000000000 / 1121476127007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (289638441 / 500000000) ≤ -Real.log (25000000000 / 44618684541) ∧
    -Real.log (25000000000 / 44618684541) ≤ (579276883 / 1000000000) := by
  have h := checkLog_sound (w := (19618684541 / 69618684541)) (n := 12)
    (lo := (289638441 / 500000000)) (hi := (579276883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44618684541 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44618684541 / 25000000000) = 1/(25000000000 / 44618684541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (289638441 / 500000000) (579276883 / 1000000000) (Real.log (44618684541 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (44618684541 / 25000000000) = -Real.log (25000000000 / 44618684541) := by
    rw [show ((44618684541 / 25000000000) : ℝ) = ((25000000000 / 44618684541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (145195147 / 250000000) ≤ -Real.log (15625000000 / 27928642757) ∧
    -Real.log (15625000000 / 27928642757) ≤ (580780589 / 1000000000) := by
  have h := checkLog_sound (w := (12303642757 / 43553642757)) (n := 12)
    (lo := (145195147 / 250000000)) (hi := (580780589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27928642757 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27928642757 / 15625000000) = 1/(15625000000 / 27928642757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (145195147 / 250000000) (580780589 / 1000000000) (Real.log (27928642757 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (27928642757 / 15625000000) = -Real.log (15625000000 / 27928642757) := by
    rw [show ((27928642757 / 15625000000) : ℝ) = ((15625000000 / 27928642757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0263

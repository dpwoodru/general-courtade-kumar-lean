import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell242
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (331016533 / 1000000000) ≤ -Real.log (5120 / 7129) ∧
    -Real.log (5120 / 7129) ≤ (165508267 / 500000000) := by
  have h := checkLog_sound (w := (2009 / 12249)) (n := 12)
    (lo := (331016533 / 1000000000)) (hi := (165508267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7129 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7129 / 5120) = 1/(5120 / 7129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (331016533 / 1000000000) (165508267 / 500000000) (Real.log (7129 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7129 / 5120) = -Real.log (5120 / 7129) := by
    rw [show ((7129 / 5120) : ℝ) = ((5120 / 7129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (498210221 / 1000000000) ≤ -Real.log (3111 / 5120) ∧
    -Real.log (3111 / 5120) ≤ (249105111 / 500000000) := by
  have h := checkLog_sound (w := (2009 / 8231)) (n := 12)
    (lo := (498210221 / 1000000000)) (hi := (249105111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3111) = 1/(3111 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-249105111 / 500000000) (-498210221 / 1000000000) (Real.log (3111 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (82648907 / 250000000) ≤ -Real.log (2560 / 3563) ∧
    -Real.log (2560 / 3563) ≤ (330595629 / 1000000000) := by
  have h := checkLog_sound (w := (1003 / 6123)) (n := 12)
    (lo := (82648907 / 250000000)) (hi := (330595629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3563 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3563 / 2560) = 1/(2560 / 3563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (82648907 / 250000000) (330595629 / 1000000000) (Real.log (3563 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3563 / 2560) = -Real.log (2560 / 3563) := by
    rw [show ((3563 / 2560) : ℝ) = ((2560 / 3563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (99449273 / 200000000) ≤ -Real.log (1557 / 2560) ∧
    -Real.log (1557 / 2560) ≤ (248623183 / 500000000) := by
  have h := checkLog_sound (w := (1003 / 4117)) (n := 12)
    (lo := (99449273 / 200000000)) (hi := (248623183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1557) = 1/(1557 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-248623183 / 500000000) (-99449273 / 200000000) (Real.log (1557 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (123014241 / 500000000) ≤ -Real.log (125000 / 159867) ∧
    -Real.log (125000 / 159867) ≤ (246028483 / 1000000000) := by
  have h := checkLog_sound (w := (34867 / 284867)) (n := 12)
    (lo := (123014241 / 500000000)) (hi := (246028483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159867 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159867 / 125000) = 1/(125000 / 159867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (123014241 / 500000000) (246028483 / 1000000000) (Real.log (159867 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (159867 / 125000) = -Real.log (125000 / 159867) := by
    rw [show ((159867 / 125000) : ℝ) = ((125000 / 159867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (16351369 / 50000000) ≤ -Real.log (90133 / 125000) ∧
    -Real.log (90133 / 125000) ≤ (327027381 / 1000000000) := by
  have h := checkLog_sound (w := (34867 / 215133)) (n := 12)
    (lo := (16351369 / 50000000)) (hi := (327027381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 90133) = 1/(90133 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-327027381 / 1000000000) (-16351369 / 50000000) (Real.log (90133 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (123180367 / 500000000) ≤ -Real.log (1000000 / 1279361) ∧
    -Real.log (1000000 / 1279361) ≤ (49272147 / 200000000) := by
  have h := checkLog_sound (w := (279361 / 2279361)) (n := 12)
    (lo := (123180367 / 500000000)) (hi := (49272147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1279361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1279361 / 1000000) = 1/(1000000 / 1279361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (123180367 / 500000000) (49272147 / 200000000) (Real.log (1279361 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1279361 / 1000000) = -Real.log (1000000 / 1279361) := by
    rw [show ((1279361 / 1000000) : ℝ) = ((1000000 / 1279361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1023803 / 3125000) ≤ -Real.log (720639 / 1000000) ∧
    -Real.log (720639 / 1000000) ≤ (327616961 / 1000000000) := by
  have h := checkLog_sound (w := (279361 / 1720639)) (n := 12)
    (lo := (1023803 / 3125000)) (hi := (327616961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 720639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 720639) = 1/(720639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-327616961 / 1000000000) (-1023803 / 3125000) (Real.log (720639 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (183638189 / 1000000000) ≤ -Real.log (1000000 / 1201581) ∧
    -Real.log (1000000 / 1201581) ≤ (18363819 / 100000000) := by
  have h := checkLog_sound (w := (201581 / 2201581)) (n := 12)
    (lo := (183638189 / 1000000000)) (hi := (18363819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1201581 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1201581 / 1000000) = 1/(1000000 / 1201581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (183638189 / 1000000000) (18363819 / 100000000) (Real.log (1201581 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1201581 / 1000000) = -Real.log (1000000 / 1201581) := by
    rw [show ((1201581 / 1000000) : ℝ) = ((1000000 / 1201581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (56280439 / 250000000) ≤ -Real.log (798419 / 1000000) ∧
    -Real.log (798419 / 1000000) ≤ (225121757 / 1000000000) := by
  have h := checkLog_sound (w := (201581 / 1798419)) (n := 12)
    (lo := (56280439 / 250000000)) (hi := (225121757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 798419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 798419) = 1/(798419 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-225121757 / 1000000000) (-56280439 / 250000000) (Real.log (798419 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (91952651 / 500000000) ≤ -Real.log (500000 / 600951) ∧
    -Real.log (500000 / 600951) ≤ (183905303 / 1000000000) := by
  have h := checkLog_sound (w := (100951 / 1100951)) (n := 12)
    (lo := (91952651 / 500000000)) (hi := (183905303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600951 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600951 / 500000) = 1/(500000 / 600951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (91952651 / 500000000) (183905303 / 1000000000) (Real.log (600951 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (600951 / 500000) = -Real.log (500000 / 600951) := by
    rw [show ((600951 / 500000) : ℝ) = ((500000 / 600951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (112761941 / 500000000) ≤ -Real.log (399049 / 500000) ∧
    -Real.log (399049 / 500000) ≤ (225523883 / 1000000000) := by
  have h := checkLog_sound (w := (100951 / 899049)) (n := 12)
    (lo := (112761941 / 500000000)) (hi := (225523883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399049) = 1/(399049 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-225523883 / 1000000000) (-112761941 / 500000000) (Real.log (399049 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (827841993 / 1000000000) ≤ -Real.log (500000000000 / 1144187540141) ∧
    -Real.log (500000000000 / 1144187540141) ≤ (165568399 / 200000000) := by
  have h := checkLog_sound (w := (144187540141 / 2144187540141)) (n := 12)
    (lo := (134694813 / 1000000000)) (hi := (67347407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1144187540141 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1144187540141 / 1000000000000) = 1/(500000000000 / 1144187540141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (827841993 / 1000000000) (165568399 / 200000000) (Real.log (1144187540141 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1144187540141 / 500000000000) = -Real.log (500000000000 / 1144187540141) := by
    rw [show ((1144187540141 / 500000000000) : ℝ) = ((500000000000 / 1144187540141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (829226753 / 1000000000) ≤ -Real.log (125000000000 / 286443265831) ∧
    -Real.log (125000000000 / 286443265831) ≤ (165845351 / 200000000) := by
  have h := checkLog_sound (w := (36443265831 / 536443265831)) (n := 12)
    (lo := (136079573 / 1000000000)) (hi := (68039787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286443265831 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(286443265831 / 250000000000) = 1/(125000000000 / 286443265831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (829226753 / 1000000000) (165845351 / 200000000) (Real.log (286443265831 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (286443265831 / 125000000000) = -Real.log (125000000000 / 286443265831) := by
    rw [show ((286443265831 / 125000000000) : ℝ) = ((125000000000 / 286443265831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (286527931 / 500000000) ≤ -Real.log (50000000000 / 88683944837) ∧
    -Real.log (50000000000 / 88683944837) ≤ (573055863 / 1000000000) := by
  have h := checkLog_sound (w := (38683944837 / 138683944837)) (n := 12)
    (lo := (286527931 / 500000000)) (hi := (573055863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88683944837 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88683944837 / 50000000000) = 1/(50000000000 / 88683944837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (286527931 / 500000000) (573055863 / 1000000000) (Real.log (88683944837 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (88683944837 / 50000000000) = -Real.log (50000000000 / 88683944837) := by
    rw [show ((88683944837 / 50000000000) : ℝ) = ((50000000000 / 88683944837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (114795539 / 200000000) ≤ -Real.log (500000000000 / 887657342997) ∧
    -Real.log (500000000000 / 887657342997) ≤ (17936803 / 31250000) := by
  have h := checkLog_sound (w := (387657342997 / 1387657342997)) (n := 12)
    (lo := (114795539 / 200000000)) (hi := (17936803 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887657342997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887657342997 / 500000000000) = 1/(500000000000 / 887657342997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (114795539 / 200000000) (17936803 / 31250000) (Real.log (887657342997 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (887657342997 / 500000000000) = -Real.log (500000000000 / 887657342997) := by
    rw [show ((887657342997 / 500000000000) : ℝ) = ((500000000000 / 887657342997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (204379973 / 500000000) ≤ -Real.log (250000000000 / 376237602061) ∧
    -Real.log (250000000000 / 376237602061) ≤ (408759947 / 1000000000) := by
  have h := checkLog_sound (w := (126237602061 / 626237602061)) (n := 12)
    (lo := (204379973 / 500000000)) (hi := (408759947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376237602061 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376237602061 / 250000000000) = 1/(250000000000 / 376237602061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (204379973 / 500000000) (408759947 / 1000000000) (Real.log (376237602061 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (376237602061 / 250000000000) = -Real.log (250000000000 / 376237602061) := by
    rw [show ((376237602061 / 250000000000) : ℝ) = ((250000000000 / 376237602061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (6397331 / 15625000) ≤ -Real.log (15625000000 / 23530592421) ∧
    -Real.log (15625000000 / 23530592421) ≤ (81885837 / 200000000) := by
  have h := checkLog_sound (w := (7905592421 / 39155592421)) (n := 12)
    (lo := (6397331 / 15625000)) (hi := (81885837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23530592421 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23530592421 / 15625000000) = 1/(15625000000 / 23530592421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (6397331 / 15625000) (81885837 / 200000000) (Real.log (23530592421 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (23530592421 / 15625000000) = -Real.log (15625000000 / 23530592421) := by
    rw [show ((23530592421 / 15625000000) : ℝ) = ((15625000000 / 23530592421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2080929 / 50000000) ≤ -Real.log (239808895599 / 250000000000) ∧
    -Real.log (239808895599 / 250000000000) ≤ (41618581 / 1000000000) := by
  have h := checkLog_sound (w := (10191104401 / 489808895599)) (n := 12)
    (lo := (2080929 / 50000000)) (hi := (41618581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239808895599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239808895599) = 1/(239808895599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-41618581 / 1000000000) (-2080929 / 50000000) (Real.log (239808895599 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (41483567 / 1000000000) ≤ -Real.log (959365100439 / 1000000000000) ∧
    -Real.log (959365100439 / 1000000000000) ≤ (2592723 / 62500000) := by
  have h := checkLog_sound (w := (40634899561 / 1959365100439)) (n := 12)
    (lo := (41483567 / 1000000000)) (hi := (2592723 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959365100439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959365100439) = 1/(959365100439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2592723 / 62500000) (-41483567 / 1000000000) (Real.log (959365100439 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell242

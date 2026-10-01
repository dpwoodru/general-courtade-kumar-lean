import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell240
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

theorem reflection_log_1_neg : (66034909 / 200000000) ≤ -Real.log (5120 / 7123) ∧
    -Real.log (5120 / 7123) ≤ (165087273 / 500000000) := by
  have h := checkLog_sound (w := (2003 / 12243)) (n := 12)
    (lo := (66034909 / 200000000)) (hi := (165087273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7123 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7123 / 5120) = 1/(5120 / 7123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66034909 / 200000000) (165087273 / 500000000) (Real.log (7123 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7123 / 5120) = -Real.log (5120 / 7123) := by
    rw [show ((7123 / 5120) : ℝ) = ((5120 / 7123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (248141719 / 500000000) ≤ -Real.log (3117 / 5120) ∧
    -Real.log (3117 / 5120) ≤ (496283439 / 1000000000) := by
  have h := checkLog_sound (w := (2003 / 8237)) (n := 12)
    (lo := (248141719 / 500000000)) (hi := (496283439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3117) = 1/(3117 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-496283439 / 1000000000) (-248141719 / 500000000) (Real.log (3117 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (164876643 / 500000000) ≤ -Real.log (64 / 89) ∧
    -Real.log (64 / 89) ≤ (329753287 / 1000000000) := by
  have h := checkLog_sound (w := (25 / 153)) (n := 12)
    (lo := (164876643 / 500000000)) (hi := (329753287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89 / 64) = 1/(64 / 89) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (164876643 / 500000000) (329753287 / 1000000000) (Real.log (89 / 64)) := by
  have h := reflection_log_3_neg
  have he : Real.log (89 / 64) = -Real.log (64 / 89) := by
    rw [show ((89 / 64) : ℝ) = ((64 / 89) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (495321437 / 1000000000) ≤ -Real.log (39 / 64) ∧
    -Real.log (39 / 64) ≤ (247660719 / 500000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 39) = 1/(39 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-247660719 / 500000000) (-495321437 / 1000000000) (Real.log (39 / 64)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (30670847 / 125000000) ≤ -Real.log (100000 / 127809) ∧
    -Real.log (100000 / 127809) ≤ (245366777 / 1000000000) := by
  have h := checkLog_sound (w := (27809 / 227809)) (n := 12)
    (lo := (30670847 / 125000000)) (hi := (245366777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127809 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127809 / 100000) = 1/(100000 / 127809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (30670847 / 125000000) (245366777 / 1000000000) (Real.log (127809 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (127809 / 100000) = -Real.log (100000 / 127809) := by
    rw [show ((127809 / 100000) : ℝ) = ((100000 / 127809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (325854801 / 1000000000) ≤ -Real.log (72191 / 100000) ∧
    -Real.log (72191 / 100000) ≤ (162927401 / 500000000) := by
  have h := checkLog_sound (w := (27809 / 172191)) (n := 12)
    (lo := (325854801 / 1000000000)) (hi := (162927401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72191) = 1/(72191 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-162927401 / 500000000) (-325854801 / 1000000000) (Real.log (72191 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122849233 / 500000000) ≤ -Real.log (500000 / 639257) ∧
    -Real.log (500000 / 639257) ≤ (245698467 / 1000000000) := by
  have h := checkLog_sound (w := (139257 / 1139257)) (n := 12)
    (lo := (122849233 / 500000000)) (hi := (245698467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639257 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639257 / 500000) = 1/(500000 / 639257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122849233 / 500000000) (245698467 / 1000000000) (Real.log (639257 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (639257 / 500000) = -Real.log (500000 / 639257) := by
    rw [show ((639257 / 500000) : ℝ) = ((500000 / 639257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5100661 / 15625000) ≤ -Real.log (360743 / 500000) ∧
    -Real.log (360743 / 500000) ≤ (65288461 / 200000000) := by
  have h := checkLog_sound (w := (139257 / 860743)) (n := 12)
    (lo := (5100661 / 15625000)) (hi := (65288461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 360743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 360743) = 1/(360743 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-65288461 / 200000000) (-5100661 / 15625000) (Real.log (360743 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (183107081 / 1000000000) ≤ -Real.log (1000000 / 1200943) ∧
    -Real.log (1000000 / 1200943) ≤ (91553541 / 500000000) := by
  have h := checkLog_sound (w := (200943 / 2200943)) (n := 12)
    (lo := (183107081 / 1000000000)) (hi := (91553541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1200943 / 1000000) = 1/(1000000 / 1200943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (183107081 / 1000000000) (91553541 / 500000000) (Real.log (1200943 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1200943 / 1000000) = -Real.log (1000000 / 1200943) := by
    rw [show ((1200943 / 1000000) : ℝ) = ((1000000 / 1200943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (56080749 / 250000000) ≤ -Real.log (799057 / 1000000) ∧
    -Real.log (799057 / 1000000) ≤ (224322997 / 1000000000) := by
  have h := checkLog_sound (w := (200943 / 1799057)) (n := 12)
    (lo := (56080749 / 250000000)) (hi := (224322997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 799057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 799057) = 1/(799057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-224322997 / 1000000000) (-56080749 / 250000000) (Real.log (799057 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (183373503 / 1000000000) ≤ -Real.log (1000000 / 1201263) ∧
    -Real.log (1000000 / 1201263) ≤ (2865211 / 15625000) := by
  have h := checkLog_sound (w := (201263 / 2201263)) (n := 12)
    (lo := (183373503 / 1000000000)) (hi := (2865211 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1201263 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1201263 / 1000000) = 1/(1000000 / 1201263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (183373503 / 1000000000) (2865211 / 15625000) (Real.log (1201263 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1201263 / 1000000) = -Real.log (1000000 / 1201263) := by
    rw [show ((1201263 / 1000000) : ℝ) = ((1000000 / 1201263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (56180887 / 250000000) ≤ -Real.log (798737 / 1000000) ∧
    -Real.log (798737 / 1000000) ≤ (224723549 / 1000000000) := by
  have h := checkLog_sound (w := (201263 / 1798737)) (n := 12)
    (lo := (56180887 / 250000000)) (hi := (224723549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 798737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 798737) = 1/(798737 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-224723549 / 1000000000) (-56180887 / 250000000) (Real.log (798737 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (825074723 / 1000000000) ≤ -Real.log (20000000000 / 45641025641) ∧
    -Real.log (20000000000 / 45641025641) ≤ (33002989 / 40000000) := by
  have h := checkLog_sound (w := (5641025641 / 85641025641)) (n := 12)
    (lo := (131927543 / 1000000000)) (hi := (16490943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45641025641 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(45641025641 / 40000000000) = 1/(20000000000 / 45641025641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (825074723 / 1000000000) (33002989 / 40000000) (Real.log (45641025641 / 20000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (45641025641 / 20000000000) = -Real.log (20000000000 / 45641025641) := by
    rw [show ((45641025641 / 20000000000) : ℝ) = ((20000000000 / 45641025641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (826457983 / 1000000000) ≤ -Real.log (500000000000 / 1142605068977) ∧
    -Real.log (500000000000 / 1142605068977) ≤ (165291597 / 200000000) := by
  have h := checkLog_sound (w := (142605068977 / 2142605068977)) (n := 12)
    (lo := (133310803 / 1000000000)) (hi := (33327701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142605068977 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1142605068977 / 1000000000000) = 1/(500000000000 / 1142605068977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (826457983 / 1000000000) (165291597 / 200000000) (Real.log (1142605068977 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1142605068977 / 500000000000) = -Real.log (500000000000 / 1142605068977) := by
    rw [show ((1142605068977 / 500000000000) : ℝ) = ((500000000000 / 1142605068977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (571221577 / 1000000000) ≤ -Real.log (500000000000 / 885214223379) ∧
    -Real.log (500000000000 / 885214223379) ≤ (285610789 / 500000000) := by
  have h := checkLog_sound (w := (385214223379 / 1385214223379)) (n := 12)
    (lo := (571221577 / 1000000000)) (hi := (285610789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885214223379 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885214223379 / 500000000000) = 1/(500000000000 / 885214223379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (571221577 / 1000000000) (285610789 / 500000000) (Real.log (885214223379 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (885214223379 / 500000000000) = -Real.log (500000000000 / 885214223379) := by
    rw [show ((885214223379 / 500000000000) : ℝ) = ((500000000000 / 885214223379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (57214077 / 100000000) ≤ -Real.log (250000000000 / 443014140261) ∧
    -Real.log (250000000000 / 443014140261) ≤ (572140771 / 1000000000) := by
  have h := checkLog_sound (w := (193014140261 / 693014140261)) (n := 12)
    (lo := (57214077 / 100000000)) (hi := (572140771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((443014140261 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(443014140261 / 250000000000) = 1/(250000000000 / 443014140261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (57214077 / 100000000) (572140771 / 1000000000) (Real.log (443014140261 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (443014140261 / 250000000000) = -Real.log (250000000000 / 443014140261) := by
    rw [show ((443014140261 / 250000000000) : ℝ) = ((250000000000 / 443014140261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (203715039 / 500000000) ≤ -Real.log (125000000000 / 187868794091) ∧
    -Real.log (125000000000 / 187868794091) ≤ (407430079 / 1000000000) := by
  have h := checkLog_sound (w := (62868794091 / 312868794091)) (n := 12)
    (lo := (203715039 / 500000000)) (hi := (407430079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187868794091 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187868794091 / 125000000000) = 1/(125000000000 / 187868794091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (203715039 / 500000000) (407430079 / 1000000000) (Real.log (187868794091 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (187868794091 / 125000000000) = -Real.log (125000000000 / 187868794091) := by
    rw [show ((187868794091 / 125000000000) : ℝ) = ((125000000000 / 187868794091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (102024263 / 250000000) ≤ -Real.log (500000000000 / 751976557991) ∧
    -Real.log (500000000000 / 751976557991) ≤ (408097053 / 1000000000) := by
  have h := checkLog_sound (w := (251976557991 / 1251976557991)) (n := 12)
    (lo := (102024263 / 250000000)) (hi := (408097053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751976557991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751976557991 / 500000000000) = 1/(500000000000 / 751976557991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (102024263 / 250000000) (408097053 / 1000000000) (Real.log (751976557991 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (751976557991 / 500000000000) = -Real.log (500000000000 / 751976557991) := by
    rw [show ((751976557991 / 500000000000) : ℝ) = ((500000000000 / 751976557991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8270009 / 200000000) ≤ -Real.log (959493204831 / 1000000000000) ∧
    -Real.log (959493204831 / 1000000000000) ≤ (20675023 / 500000000) := by
  have h := checkLog_sound (w := (40506795169 / 1959493204831)) (n := 12)
    (lo := (8270009 / 200000000)) (hi := (20675023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959493204831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959493204831) = 1/(959493204831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20675023 / 500000000) (-8270009 / 200000000) (Real.log (959493204831 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8243183 / 200000000) ≤ -Real.log (959621910751 / 1000000000000) ∧
    -Real.log (959621910751 / 1000000000000) ≤ (10303979 / 250000000) := by
  have h := checkLog_sound (w := (40378089249 / 1959621910751)) (n := 12)
    (lo := (8243183 / 200000000)) (hi := (10303979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959621910751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959621910751) = 1/(959621910751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10303979 / 250000000) (-8243183 / 200000000) (Real.log (959621910751 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell240

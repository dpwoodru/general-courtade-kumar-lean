import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0411
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

theorem reflection_log_1_neg : (197585329 / 1000000000) ≤ -Real.log (10240 / 12477) ∧
    -Real.log (10240 / 12477) ≤ (19758533 / 100000000) := by
  have h := checkLog_sound (w := (2237 / 22717)) (n := 12)
    (lo := (197585329 / 1000000000)) (hi := (19758533 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12477 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12477 / 10240) = 1/(10240 / 12477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (197585329 / 1000000000) (19758533 / 100000000) (Real.log (12477 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12477 / 10240) = -Real.log (10240 / 12477) := by
    rw [show ((12477 / 10240) : ℝ) = ((10240 / 12477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (61621287 / 250000000) ≤ -Real.log (8003 / 10240) ∧
    -Real.log (8003 / 10240) ≤ (246485149 / 1000000000) := by
  have h := checkLog_sound (w := (2237 / 18243)) (n := 12)
    (lo := (61621287 / 250000000)) (hi := (246485149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8003) = 1/(8003 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-246485149 / 1000000000) (-61621287 / 250000000) (Real.log (8003 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (98672429 / 500000000) ≤ -Real.log (5120 / 6237) ∧
    -Real.log (5120 / 6237) ≤ (197344859 / 1000000000) := by
  have h := checkLog_sound (w := (1117 / 11357)) (n := 12)
    (lo := (98672429 / 500000000)) (hi := (197344859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6237 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6237 / 5120) = 1/(5120 / 6237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (98672429 / 500000000) (197344859 / 1000000000) (Real.log (6237 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6237 / 5120) = -Real.log (5120 / 6237) := by
    rw [show ((6237 / 5120) : ℝ) = ((5120 / 6237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (246110359 / 1000000000) ≤ -Real.log (4003 / 5120) ∧
    -Real.log (4003 / 5120) ≤ (6152759 / 25000000) := by
  have h := checkLog_sound (w := (1117 / 9123)) (n := 12)
    (lo := (246110359 / 1000000000)) (hi := (6152759 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4003) = 1/(4003 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6152759 / 25000000) (-246110359 / 1000000000) (Real.log (4003 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (362497801 / 1000000000) ≤ -Real.log (5120 / 7357) ∧
    -Real.log (5120 / 7357) ≤ (181248901 / 500000000) := by
  have h := checkLog_sound (w := (2237 / 12477)) (n := 12)
    (lo := (362497801 / 1000000000)) (hi := (181248901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7357 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7357 / 5120) = 1/(5120 / 7357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (362497801 / 1000000000) (181248901 / 500000000) (Real.log (7357 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7357 / 5120) = -Real.log (5120 / 7357) := by
    rw [show ((7357 / 5120) : ℝ) = ((5120 / 7357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (28716151 / 50000000) ≤ -Real.log (2883 / 5120) ∧
    -Real.log (2883 / 5120) ≤ (574323021 / 1000000000) := by
  have h := checkLog_sound (w := (2237 / 8003)) (n := 12)
    (lo := (28716151 / 50000000)) (hi := (574323021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2883) = 1/(2883 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-574323021 / 1000000000) (-28716151 / 50000000) (Real.log (2883 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (362089943 / 1000000000) ≤ -Real.log (2560 / 3677) ∧
    -Real.log (2560 / 3677) ≤ (45261243 / 125000000) := by
  have h := checkLog_sound (w := (1117 / 6237)) (n := 12)
    (lo := (362089943 / 1000000000)) (hi := (45261243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3677 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3677 / 2560) = 1/(2560 / 3677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (362089943 / 1000000000) (45261243 / 125000000) (Real.log (3677 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3677 / 2560) = -Real.log (2560 / 3677) := by
    rw [show ((3677 / 2560) : ℝ) = ((2560 / 3677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (286641489 / 500000000) ≤ -Real.log (1443 / 2560) ∧
    -Real.log (1443 / 2560) ≤ (573282979 / 1000000000) := by
  have h := checkLog_sound (w := (1117 / 4003)) (n := 12)
    (lo := (286641489 / 500000000)) (hi := (573282979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1443) = 1/(1443 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-573282979 / 1000000000) (-286641489 / 500000000) (Real.log (1443 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (270937409 / 1000000000) ≤ -Real.log (1000000 / 1311193) ∧
    -Real.log (1000000 / 1311193) ≤ (27093741 / 100000000) := by
  have h := checkLog_sound (w := (311193 / 2311193)) (n := 12)
    (lo := (270937409 / 1000000000)) (hi := (27093741 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311193 / 1000000) = 1/(1000000 / 1311193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (270937409 / 1000000000) (27093741 / 100000000) (Real.log (1311193 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1311193 / 1000000) = -Real.log (1000000 / 1311193) := by
    rw [show ((1311193 / 1000000) : ℝ) = ((1000000 / 1311193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (372794163 / 1000000000) ≤ -Real.log (688807 / 1000000) ∧
    -Real.log (688807 / 1000000) ≤ (93198541 / 250000000) := by
  have h := checkLog_sound (w := (311193 / 1688807)) (n := 12)
    (lo := (372794163 / 1000000000)) (hi := (93198541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 688807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 688807) = 1/(688807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-93198541 / 250000000) (-372794163 / 1000000000) (Real.log (688807 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135631507 / 500000000) ≤ -Real.log (50000 / 65581) ∧
    -Real.log (50000 / 65581) ≤ (54252603 / 200000000) := by
  have h := checkLog_sound (w := (15581 / 115581)) (n := 12)
    (lo := (135631507 / 500000000)) (hi := (54252603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65581 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65581 / 50000) = 1/(50000 / 65581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135631507 / 500000000) (54252603 / 200000000) (Real.log (65581 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (65581 / 50000) = -Real.log (50000 / 65581) := by
    rw [show ((65581 / 50000) : ℝ) = ((50000 / 65581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (373414267 / 1000000000) ≤ -Real.log (34419 / 50000) ∧
    -Real.log (34419 / 50000) ≤ (93353567 / 250000000) := by
  have h := checkLog_sound (w := (15581 / 84419)) (n := 12)
    (lo := (373414267 / 1000000000)) (hi := (93353567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 34419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 34419) = 1/(34419 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-93353567 / 250000000) (-373414267 / 1000000000) (Real.log (34419 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (50961231 / 250000000) ≤ -Real.log (250000 / 306527) ∧
    -Real.log (250000 / 306527) ≤ (8153797 / 40000000) := by
  have h := checkLog_sound (w := (56527 / 556527)) (n := 12)
    (lo := (50961231 / 250000000)) (hi := (8153797 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306527 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306527 / 250000) = 1/(250000 / 306527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (50961231 / 250000000) (8153797 / 40000000) (Real.log (306527 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (306527 / 250000) = -Real.log (250000 / 306527) := by
    rw [show ((306527 / 250000) : ℝ) = ((250000 / 306527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (5126459 / 20000000) ≤ -Real.log (193473 / 250000) ∧
    -Real.log (193473 / 250000) ≤ (256322951 / 1000000000) := by
  have h := checkLog_sound (w := (56527 / 443473)) (n := 12)
    (lo := (5126459 / 20000000)) (hi := (256322951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193473) = 1/(193473 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-256322951 / 1000000000) (-5126459 / 20000000) (Real.log (193473 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (102056201 / 500000000) ≤ -Real.log (250000 / 306609) ∧
    -Real.log (250000 / 306609) ≤ (204112403 / 1000000000) := by
  have h := checkLog_sound (w := (56609 / 556609)) (n := 12)
    (lo := (102056201 / 500000000)) (hi := (204112403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306609 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306609 / 250000) = 1/(250000 / 306609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (102056201 / 500000000) (204112403 / 1000000000) (Real.log (306609 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (306609 / 250000) = -Real.log (250000 / 306609) := by
    rw [show ((306609 / 250000) : ℝ) = ((250000 / 306609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (256746871 / 1000000000) ≤ -Real.log (193391 / 250000) ∧
    -Real.log (193391 / 250000) ≤ (32093359 / 125000000) := by
  have h := checkLog_sound (w := (56609 / 443391)) (n := 12)
    (lo := (256746871 / 1000000000)) (hi := (32093359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193391) = 1/(193391 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-32093359 / 125000000) (-256746871 / 1000000000) (Real.log (193391 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (643731573 / 1000000000) ≤ -Real.log (50000000000 / 95178547837) ∧
    -Real.log (50000000000 / 95178547837) ≤ (321865787 / 500000000) := by
  have h := checkLog_sound (w := (45178547837 / 145178547837)) (n := 12)
    (lo := (643731573 / 1000000000)) (hi := (321865787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95178547837 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95178547837 / 50000000000) = 1/(50000000000 / 95178547837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (643731573 / 1000000000) (321865787 / 500000000) (Real.log (95178547837 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (95178547837 / 50000000000) = -Real.log (50000000000 / 95178547837) := by
    rw [show ((95178547837 / 50000000000) : ℝ) = ((50000000000 / 95178547837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (322338641 / 500000000) ≤ -Real.log (100000000000 / 190537203289) ∧
    -Real.log (100000000000 / 190537203289) ≤ (644677283 / 1000000000) := by
  have h := checkLog_sound (w := (90537203289 / 290537203289)) (n := 12)
    (lo := (322338641 / 500000000)) (hi := (644677283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190537203289 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190537203289 / 100000000000) = 1/(100000000000 / 190537203289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (322338641 / 500000000) (644677283 / 1000000000) (Real.log (190537203289 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (190537203289 / 100000000000) = -Real.log (100000000000 / 190537203289) := by
    rw [show ((190537203289 / 100000000000) : ℝ) = ((100000000000 / 190537203289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (230083937 / 500000000) ≤ -Real.log (125000000000 / 198042491717) ∧
    -Real.log (125000000000 / 198042491717) ≤ (3681343 / 8000000) := by
  have h := checkLog_sound (w := (73042491717 / 323042491717)) (n := 12)
    (lo := (230083937 / 500000000)) (hi := (3681343 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198042491717 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198042491717 / 125000000000) = 1/(125000000000 / 198042491717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (230083937 / 500000000) (3681343 / 8000000) (Real.log (198042491717 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (198042491717 / 125000000000) = -Real.log (125000000000 / 198042491717) := by
    rw [show ((198042491717 / 125000000000) : ℝ) = ((125000000000 / 198042491717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (460859273 / 1000000000) ≤ -Real.log (250000000000 / 396358930871) ∧
    -Real.log (250000000000 / 396358930871) ≤ (230429637 / 500000000) := by
  have h := checkLog_sound (w := (146358930871 / 646358930871)) (n := 12)
    (lo := (460859273 / 1000000000)) (hi := (230429637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396358930871 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396358930871 / 250000000000) = 1/(250000000000 / 396358930871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (460859273 / 1000000000) (230429637 / 500000000) (Real.log (396358930871 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (396358930871 / 250000000000) = -Real.log (250000000000 / 396358930871) := by
    rw [show ((396358930871 / 250000000000) : ℝ) = ((250000000000 / 396358930871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0411

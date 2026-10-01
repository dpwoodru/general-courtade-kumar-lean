import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell174
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

theorem reflection_log_1_neg : (301983613 / 1000000000) ≤ -Real.log (1024 / 1385) ∧
    -Real.log (1024 / 1385) ≤ (150991807 / 500000000) := by
  have h := checkLog_sound (w := (361 / 2409)) (n := 12)
    (lo := (301983613 / 1000000000)) (hi := (150991807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1385 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1385 / 1024) = 1/(1024 / 1385) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (301983613 / 1000000000) (150991807 / 500000000) (Real.log (1385 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1385 / 1024) = -Real.log (1024 / 1385) := by
    rw [show ((1385 / 1024) : ℝ) = ((1024 / 1385) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (86939363 / 200000000) ≤ -Real.log (663 / 1024) ∧
    -Real.log (663 / 1024) ≤ (27168551 / 62500000) := by
  have h := checkLog_sound (w := (361 / 1687)) (n := 12)
    (lo := (86939363 / 200000000)) (hi := (27168551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 663) = 1/(663 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-27168551 / 62500000) (-86939363 / 200000000) (Real.log (663 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (150775153 / 500000000) ≤ -Real.log (2560 / 3461) ∧
    -Real.log (2560 / 3461) ≤ (301550307 / 1000000000) := by
  have h := checkLog_sound (w := (901 / 6021)) (n := 12)
    (lo := (150775153 / 500000000)) (hi := (301550307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3461 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3461 / 2560) = 1/(2560 / 3461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (150775153 / 500000000) (301550307 / 1000000000) (Real.log (3461 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3461 / 2560) = -Real.log (2560 / 3461) := by
    rw [show ((3461 / 2560) : ℝ) = ((2560 / 3461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (433792247 / 1000000000) ≤ -Real.log (1659 / 2560) ∧
    -Real.log (1659 / 2560) ≤ (54224031 / 125000000) := by
  have h := checkLog_sound (w := (901 / 4219)) (n := 12)
    (lo := (433792247 / 1000000000)) (hi := (54224031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1659) = 1/(1659 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-54224031 / 125000000) (-433792247 / 1000000000) (Real.log (1659 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (44664387 / 200000000) ≤ -Real.log (1000000 / 1250223) ∧
    -Real.log (1000000 / 1250223) ≤ (13957621 / 62500000) := by
  have h := checkLog_sound (w := (250223 / 2250223)) (n := 12)
    (lo := (44664387 / 200000000)) (hi := (13957621 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250223 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250223 / 1000000) = 1/(1000000 / 1250223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (44664387 / 200000000) (13957621 / 62500000) (Real.log (1250223 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1250223 / 1000000) = -Real.log (1000000 / 1250223) := by
    rw [show ((1250223 / 1000000) : ℝ) = ((1000000 / 1250223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (287979449 / 1000000000) ≤ -Real.log (749777 / 1000000) ∧
    -Real.log (749777 / 1000000) ≤ (5759589 / 20000000) := by
  have h := checkLog_sound (w := (250223 / 1749777)) (n := 12)
    (lo := (287979449 / 1000000000)) (hi := (5759589 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 749777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 749777) = 1/(749777 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5759589 / 20000000) (-287979449 / 1000000000) (Real.log (749777 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (111829709 / 500000000) ≤ -Real.log (200000 / 250129) ∧
    -Real.log (200000 / 250129) ≤ (223659419 / 1000000000) := by
  have h := checkLog_sound (w := (50129 / 450129)) (n := 12)
    (lo := (111829709 / 500000000)) (hi := (223659419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250129 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250129 / 200000) = 1/(200000 / 250129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (111829709 / 500000000) (223659419 / 1000000000) (Real.log (250129 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (250129 / 200000) = -Real.log (200000 / 250129) := by
    rw [show ((250129 / 200000) : ℝ) = ((200000 / 250129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (144271221 / 500000000) ≤ -Real.log (149871 / 200000) ∧
    -Real.log (149871 / 200000) ≤ (288542443 / 1000000000) := by
  have h := checkLog_sound (w := (50129 / 349871)) (n := 12)
    (lo := (144271221 / 500000000)) (hi := (288542443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 149871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 149871) = 1/(149871 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-288542443 / 1000000000) (-144271221 / 500000000) (Real.log (149871 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (82781371 / 500000000) ≤ -Real.log (1000000 / 1180057) ∧
    -Real.log (1000000 / 1180057) ≤ (165562743 / 1000000000) := by
  have h := checkLog_sound (w := (180057 / 2180057)) (n := 12)
    (lo := (82781371 / 500000000)) (hi := (165562743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180057 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1180057 / 1000000) = 1/(1000000 / 1180057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (82781371 / 500000000) (165562743 / 1000000000) (Real.log (1180057 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1180057 / 1000000) = -Real.log (1000000 / 1180057) := by
    rw [show ((1180057 / 1000000) : ℝ) = ((1000000 / 1180057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (198520453 / 1000000000) ≤ -Real.log (819943 / 1000000) ∧
    -Real.log (819943 / 1000000) ≤ (99260227 / 500000000) := by
  have h := checkLog_sound (w := (180057 / 1819943)) (n := 12)
    (lo := (198520453 / 1000000000)) (hi := (99260227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 819943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 819943) = 1/(819943 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-99260227 / 500000000) (-198520453 / 1000000000) (Real.log (819943 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (165829643 / 1000000000) ≤ -Real.log (250000 / 295093) ∧
    -Real.log (250000 / 295093) ≤ (41457411 / 250000000) := by
  have h := checkLog_sound (w := (45093 / 545093)) (n := 12)
    (lo := (165829643 / 1000000000)) (hi := (41457411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295093 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295093 / 250000) = 1/(250000 / 295093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (165829643 / 1000000000) (41457411 / 250000000) (Real.log (295093 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (295093 / 250000) = -Real.log (250000 / 295093) := by
    rw [show ((295093 / 250000) : ℝ) = ((250000 / 295093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1989047 / 10000000) ≤ -Real.log (204907 / 250000) ∧
    -Real.log (204907 / 250000) ≤ (198904701 / 1000000000) := by
  have h := checkLog_sound (w := (45093 / 454907)) (n := 12)
    (lo := (1989047 / 10000000)) (hi := (198904701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204907) = 1/(204907 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-198904701 / 1000000000) (-1989047 / 10000000) (Real.log (204907 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (91917819 / 125000000) ≤ -Real.log (500000000000 / 1043098251959) ∧
    -Real.log (500000000000 / 1043098251959) ≤ (367671277 / 500000000) := by
  have h := checkLog_sound (w := (43098251959 / 2043098251959)) (n := 12)
    (lo := (10548843 / 250000000)) (hi := (42195373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1043098251959 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1043098251959 / 1000000000000) = 1/(500000000000 / 1043098251959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (91917819 / 125000000) (367671277 / 500000000) (Real.log (1043098251959 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1043098251959 / 500000000000) = -Real.log (500000000000 / 1043098251959) := by
    rw [show ((1043098251959 / 500000000000) : ℝ) = ((500000000000 / 1043098251959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (736680427 / 1000000000) ≤ -Real.log (250000000000 / 522247360483) ∧
    -Real.log (250000000000 / 522247360483) ≤ (736680429 / 1000000000) := by
  have h := checkLog_sound (w := (22247360483 / 1022247360483)) (n := 12)
    (lo := (43533247 / 1000000000)) (hi := (680207 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((522247360483 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(522247360483 / 500000000000) = 1/(250000000000 / 522247360483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (736680427 / 1000000000) (736680429 / 1000000000) (Real.log (522247360483 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (522247360483 / 250000000000) = -Real.log (250000000000 / 522247360483) := by
    rw [show ((522247360483 / 250000000000) : ℝ) = ((250000000000 / 522247360483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (102260277 / 200000000) ≤ -Real.log (62500000000 / 104216236961) ∧
    -Real.log (62500000000 / 104216236961) ≤ (255650693 / 500000000) := by
  have h := checkLog_sound (w := (41716236961 / 166716236961)) (n := 12)
    (lo := (102260277 / 200000000)) (hi := (255650693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104216236961 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104216236961 / 62500000000) = 1/(62500000000 / 104216236961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (102260277 / 200000000) (255650693 / 500000000) (Real.log (104216236961 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (104216236961 / 62500000000) = -Real.log (62500000000 / 104216236961) := by
    rw [show ((104216236961 / 62500000000) : ℝ) = ((62500000000 / 104216236961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25610093 / 50000000) ≤ -Real.log (500000000000 / 834480986983) ∧
    -Real.log (500000000000 / 834480986983) ≤ (512201861 / 1000000000) := by
  have h := checkLog_sound (w := (334480986983 / 1334480986983)) (n := 12)
    (lo := (25610093 / 50000000)) (hi := (512201861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834480986983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(834480986983 / 500000000000) = 1/(500000000000 / 834480986983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (25610093 / 50000000) (512201861 / 1000000000) (Real.log (834480986983 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (834480986983 / 500000000000) = -Real.log (500000000000 / 834480986983) := by
    rw [show ((834480986983 / 500000000000) : ℝ) = ((500000000000 / 834480986983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (72816639 / 200000000) ≤ -Real.log (31250000000 / 44974810749) ∧
    -Real.log (31250000000 / 44974810749) ≤ (91020799 / 250000000) := by
  have h := checkLog_sound (w := (13724810749 / 76224810749)) (n := 12)
    (lo := (72816639 / 200000000)) (hi := (91020799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44974810749 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44974810749 / 31250000000) = 1/(31250000000 / 44974810749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (72816639 / 200000000) (91020799 / 250000000) (Real.log (44974810749 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (44974810749 / 31250000000) = -Real.log (31250000000 / 44974810749) := by
    rw [show ((44974810749 / 31250000000) : ℝ) = ((31250000000 / 44974810749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (364734343 / 1000000000) ≤ -Real.log (500000000000 / 720065688337) ∧
    -Real.log (500000000000 / 720065688337) ≤ (45591793 / 125000000) := by
  have h := checkLog_sound (w := (220065688337 / 1220065688337)) (n := 12)
    (lo := (364734343 / 1000000000)) (hi := (45591793 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720065688337 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720065688337 / 500000000000) = 1/(500000000000 / 720065688337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (364734343 / 1000000000) (45591793 / 125000000) (Real.log (720065688337 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (720065688337 / 500000000000) = -Real.log (500000000000 / 720065688337) := by
    rw [show ((720065688337 / 500000000000) : ℝ) = ((500000000000 / 720065688337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33075057 / 1000000000) ≤ -Real.log (60466621351 / 62500000000) ∧
    -Real.log (60466621351 / 62500000000) ≤ (16537529 / 500000000) := by
  have h := checkLog_sound (w := (2033378649 / 122966621351)) (n := 12)
    (lo := (33075057 / 1000000000)) (hi := (16537529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60466621351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60466621351) = 1/(60466621351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16537529 / 500000000) (-33075057 / 1000000000) (Real.log (60466621351 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3295771 / 100000000) ≤ -Real.log (967579476751 / 1000000000000) ∧
    -Real.log (967579476751 / 1000000000000) ≤ (32957711 / 1000000000) := by
  have h := checkLog_sound (w := (32420523249 / 1967579476751)) (n := 12)
    (lo := (3295771 / 100000000)) (hi := (32957711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967579476751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967579476751) = 1/(967579476751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32957711 / 1000000000) (-3295771 / 100000000) (Real.log (967579476751 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell174

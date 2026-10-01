import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell228
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

theorem reflection_log_1_neg : (2031923 / 6250000) ≤ -Real.log (5120 / 7087) ∧
    -Real.log (5120 / 7087) ≤ (325107681 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 12207)) (n := 12)
    (lo := (2031923 / 6250000)) (hi := (325107681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7087 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7087 / 5120) = 1/(5120 / 7087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2031923 / 6250000) (325107681 / 1000000000) (Real.log (7087 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7087 / 5120) = -Real.log (5120 / 7087) := by
    rw [show ((7087 / 5120) : ℝ) = ((5120 / 7087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (242400029 / 500000000) ≤ -Real.log (3153 / 5120) ∧
    -Real.log (3153 / 5120) ≤ (484800059 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 8273)) (n := 12)
    (lo := (242400029 / 500000000)) (hi := (484800059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3153) = 1/(3153 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-484800059 / 1000000000) (-242400029 / 500000000) (Real.log (3153 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8117107 / 25000000) ≤ -Real.log (1280 / 1771) ∧
    -Real.log (1280 / 1771) ≤ (324684281 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 3051)) (n := 12)
    (lo := (8117107 / 25000000)) (hi := (324684281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1771 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1771 / 1280) = 1/(1280 / 1771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8117107 / 25000000) (324684281 / 1000000000) (Real.log (1771 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1771 / 1280) = -Real.log (1280 / 1771) := by
    rw [show ((1771 / 1280) : ℝ) = ((1280 / 1771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (120962259 / 250000000) ≤ -Real.log (789 / 1280) ∧
    -Real.log (789 / 1280) ≤ (483849037 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 2069)) (n := 12)
    (lo := (120962259 / 250000000)) (hi := (483849037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 789) = 1/(789 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-483849037 / 1000000000) (-120962259 / 250000000) (Real.log (789 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (241387317 / 1000000000) ≤ -Real.log (500000 / 636507) ∧
    -Real.log (500000 / 636507) ≤ (120693659 / 500000000) := by
  have h := checkLog_sound (w := (136507 / 1136507)) (n := 12)
    (lo := (241387317 / 1000000000)) (hi := (120693659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636507 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636507 / 500000) = 1/(500000 / 636507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (241387317 / 1000000000) (120693659 / 500000000) (Real.log (636507 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (636507 / 500000) = -Real.log (500000 / 636507) := by
    rw [show ((636507 / 500000) : ℝ) = ((500000 / 636507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (159424029 / 500000000) ≤ -Real.log (363493 / 500000) ∧
    -Real.log (363493 / 500000) ≤ (318848059 / 1000000000) := by
  have h := checkLog_sound (w := (136507 / 863493)) (n := 12)
    (lo := (159424029 / 500000000)) (hi := (318848059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 363493) = 1/(363493 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-318848059 / 1000000000) (-159424029 / 500000000) (Real.log (363493 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (241720329 / 1000000000) ≤ -Real.log (500000 / 636719) ∧
    -Real.log (500000 / 636719) ≤ (24172033 / 100000000) := by
  have h := checkLog_sound (w := (136719 / 1136719)) (n := 12)
    (lo := (241720329 / 1000000000)) (hi := (24172033 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636719 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636719 / 500000) = 1/(500000 / 636719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (241720329 / 1000000000) (24172033 / 100000000) (Real.log (636719 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (636719 / 500000) = -Real.log (500000 / 636719) := by
    rw [show ((636719 / 500000) : ℝ) = ((500000 / 636719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (159715729 / 500000000) ≤ -Real.log (363281 / 500000) ∧
    -Real.log (363281 / 500000) ≤ (319431459 / 1000000000) := by
  have h := checkLog_sound (w := (136719 / 863281)) (n := 12)
    (lo := (159715729 / 500000000)) (hi := (319431459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 363281) = 1/(363281 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-319431459 / 1000000000) (-159715729 / 500000000) (Real.log (363281 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (44979459 / 250000000) ≤ -Real.log (1000000 / 1197119) ∧
    -Real.log (1000000 / 1197119) ≤ (179917837 / 1000000000) := by
  have h := checkLog_sound (w := (197119 / 2197119)) (n := 12)
    (lo := (44979459 / 250000000)) (hi := (179917837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197119 / 1000000) = 1/(1000000 / 1197119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (44979459 / 250000000) (179917837 / 1000000000) (Real.log (1197119 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1197119 / 1000000) = -Real.log (1000000 / 1197119) := by
    rw [show ((1197119 / 1000000) : ℝ) = ((1000000 / 1197119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21954877 / 100000000) ≤ -Real.log (802881 / 1000000) ∧
    -Real.log (802881 / 1000000) ≤ (219548771 / 1000000000) := by
  have h := checkLog_sound (w := (197119 / 1802881)) (n := 12)
    (lo := (21954877 / 100000000)) (hi := (219548771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802881) = 1/(802881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-219548771 / 1000000000) (-21954877 / 100000000) (Real.log (802881 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (180185109 / 1000000000) ≤ -Real.log (1000000 / 1197439) ∧
    -Real.log (1000000 / 1197439) ≤ (18018511 / 100000000) := by
  have h := checkLog_sound (w := (197439 / 2197439)) (n := 12)
    (lo := (180185109 / 1000000000)) (hi := (18018511 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197439 / 1000000) = 1/(1000000 / 1197439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (180185109 / 1000000000) (18018511 / 100000000) (Real.log (1197439 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1197439 / 1000000) = -Real.log (1000000 / 1197439) := by
    rw [show ((1197439 / 1000000) : ℝ) = ((1000000 / 1197439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (109973707 / 500000000) ≤ -Real.log (802561 / 1000000) ∧
    -Real.log (802561 / 1000000) ≤ (43989483 / 200000000) := by
  have h := checkLog_sound (w := (197439 / 1802561)) (n := 12)
    (lo := (109973707 / 500000000)) (hi := (43989483 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802561) = 1/(802561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-43989483 / 200000000) (-109973707 / 500000000) (Real.log (802561 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (202133329 / 250000000) ≤ -Real.log (500000000000 / 1122306717363) ∧
    -Real.log (500000000000 / 1122306717363) ≤ (404266659 / 500000000) := by
  have h := checkLog_sound (w := (122306717363 / 2122306717363)) (n := 12)
    (lo := (14423267 / 125000000)) (hi := (115386137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1122306717363 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1122306717363 / 1000000000000) = 1/(500000000000 / 1122306717363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (202133329 / 250000000) (404266659 / 500000000) (Real.log (1122306717363 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1122306717363 / 500000000000) = -Real.log (500000000000 / 1122306717363) := by
    rw [show ((1122306717363 / 500000000000) : ℝ) = ((500000000000 / 1122306717363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (404953869 / 500000000) ≤ -Real.log (500000000000 / 1123850301301) ∧
    -Real.log (500000000000 / 1123850301301) ≤ (40495387 / 50000000) := by
  have h := checkLog_sound (w := (123850301301 / 2123850301301)) (n := 12)
    (lo := (58380279 / 500000000)) (hi := (116760559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1123850301301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1123850301301 / 1000000000000) = 1/(500000000000 / 1123850301301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (404953869 / 500000000) (40495387 / 50000000) (Real.log (1123850301301 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1123850301301 / 500000000000) = -Real.log (500000000000 / 1123850301301) := by
    rw [show ((1123850301301 / 500000000000) : ℝ) = ((500000000000 / 1123850301301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (35014711 / 62500000) ≤ -Real.log (250000000000 / 437771153777) ∧
    -Real.log (250000000000 / 437771153777) ≤ (560235377 / 1000000000) := by
  have h := checkLog_sound (w := (187771153777 / 687771153777)) (n := 12)
    (lo := (35014711 / 62500000)) (hi := (560235377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437771153777 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437771153777 / 250000000000) = 1/(250000000000 / 437771153777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (35014711 / 62500000) (560235377 / 1000000000) (Real.log (437771153777 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (437771153777 / 250000000000) = -Real.log (250000000000 / 437771153777) := by
    rw [show ((437771153777 / 250000000000) : ℝ) = ((250000000000 / 437771153777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (140287947 / 250000000) ≤ -Real.log (15625000000 / 27385782287) ∧
    -Real.log (15625000000 / 27385782287) ≤ (561151789 / 1000000000) := by
  have h := checkLog_sound (w := (11760782287 / 43010782287)) (n := 12)
    (lo := (140287947 / 250000000)) (hi := (561151789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27385782287 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27385782287 / 15625000000) = 1/(15625000000 / 27385782287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (140287947 / 250000000) (561151789 / 1000000000) (Real.log (27385782287 / 15625000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (27385782287 / 15625000000) = -Real.log (15625000000 / 27385782287) := by
    rw [show ((27385782287 / 15625000000) : ℝ) = ((15625000000 / 27385782287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (399466607 / 1000000000) ≤ -Real.log (25000000000 / 37275729529) ∧
    -Real.log (25000000000 / 37275729529) ≤ (24966663 / 62500000) := by
  have h := checkLog_sound (w := (12275729529 / 62275729529)) (n := 12)
    (lo := (399466607 / 1000000000)) (hi := (24966663 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37275729529 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37275729529 / 25000000000) = 1/(25000000000 / 37275729529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (399466607 / 1000000000) (24966663 / 62500000) (Real.log (37275729529 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (37275729529 / 25000000000) = -Real.log (25000000000 / 37275729529) := by
    rw [show ((37275729529 / 25000000000) : ℝ) = ((25000000000 / 37275729529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (400132523 / 1000000000) ≤ -Real.log (4000000000 / 5968089653) ∧
    -Real.log (4000000000 / 5968089653) ≤ (100033131 / 250000000) := by
  have h := checkLog_sound (w := (1968089653 / 9968089653)) (n := 12)
    (lo := (400132523 / 1000000000)) (hi := (100033131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5968089653 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5968089653 / 4000000000) = 1/(4000000000 / 5968089653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (400132523 / 1000000000) (100033131 / 250000000) (Real.log (5968089653 / 4000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5968089653 / 4000000000) = -Real.log (4000000000 / 5968089653) := by
    rw [show ((5968089653 / 4000000000) : ℝ) = ((4000000000 / 5968089653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (310643 / 7812500) ≤ -Real.log (961017841279 / 1000000000000) ∧
    -Real.log (961017841279 / 1000000000000) ≤ (7952461 / 200000000) := by
  have h := checkLog_sound (w := (38982158721 / 1961017841279)) (n := 12)
    (lo := (310643 / 7812500)) (hi := (7952461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961017841279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961017841279) = 1/(961017841279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-7952461 / 200000000) (-310643 / 7812500) (Real.log (961017841279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (39630933 / 1000000000) ≤ -Real.log (961144099839 / 1000000000000) ∧
    -Real.log (961144099839 / 1000000000000) ≤ (19815467 / 500000000) := by
  have h := checkLog_sound (w := (38855900161 / 1961144099839)) (n := 12)
    (lo := (39630933 / 1000000000)) (hi := (19815467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961144099839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961144099839) = 1/(961144099839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19815467 / 500000000) (-39630933 / 1000000000) (Real.log (961144099839 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell228

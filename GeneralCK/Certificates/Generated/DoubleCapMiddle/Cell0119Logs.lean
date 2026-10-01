import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0119
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

theorem reflection_log_1_neg : (317316721 / 1000000000) ≤ -Real.log (640 / 879) ∧
    -Real.log (640 / 879) ≤ (158658361 / 500000000) := by
  have h := checkLog_sound (w := (239 / 1519)) (n := 12)
    (lo := (317316721 / 1000000000)) (hi := (158658361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879 / 640) = 1/(640 / 879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (317316721 / 1000000000) (158658361 / 500000000) (Real.log (879 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (879 / 640) = -Real.log (640 / 879) := by
    rw [show ((879 / 640) : ℝ) = ((640 / 879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (467506749 / 1000000000) ≤ -Real.log (401 / 640) ∧
    -Real.log (401 / 640) ≤ (1870027 / 4000000) := by
  have h := checkLog_sound (w := (239 / 1041)) (n := 12)
    (lo := (467506749 / 1000000000)) (hi := (1870027 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 401) = 1/(401 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1870027 / 4000000) (-467506749 / 1000000000) (Real.log (401 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (158231557 / 500000000) ≤ -Real.log (2560 / 3513) ∧
    -Real.log (2560 / 3513) ≤ (63292623 / 200000000) := by
  have h := checkLog_sound (w := (953 / 6073)) (n := 12)
    (lo := (158231557 / 500000000)) (hi := (63292623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3513 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3513 / 2560) = 1/(2560 / 3513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (158231557 / 500000000) (63292623 / 200000000) (Real.log (3513 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3513 / 2560) = -Real.log (2560 / 3513) := by
    rw [show ((3513 / 2560) : ℝ) = ((2560 / 3513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (465638171 / 1000000000) ≤ -Real.log (1607 / 2560) ∧
    -Real.log (1607 / 2560) ≤ (116409543 / 250000000) := by
  have h := checkLog_sound (w := (953 / 4167)) (n := 12)
    (lo := (465638171 / 1000000000)) (hi := (116409543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1607) = 1/(1607 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-116409543 / 250000000) (-465638171 / 1000000000) (Real.log (1607 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (557828477 / 1000000000) ≤ -Real.log (320 / 559) ∧
    -Real.log (320 / 559) ≤ (278914239 / 500000000) := by
  have h := checkLog_sound (w := (239 / 879)) (n := 12)
    (lo := (557828477 / 1000000000)) (hi := (278914239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559 / 320) = 1/(320 / 559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (557828477 / 1000000000) (278914239 / 500000000) (Real.log (559 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (559 / 320) = -Real.log (320 / 559) := by
    rw [show ((559 / 320) : ℝ) = ((320 / 559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (8586699 / 6250000) ≤ -Real.log (81 / 320) ∧
    -Real.log (81 / 320) ≤ (686935921 / 500000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 81) = 1/(81 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-686935921 / 500000000) (-8586699 / 6250000) (Real.log (81 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (278242947 / 500000000) ≤ -Real.log (1280 / 2233) ∧
    -Real.log (1280 / 2233) ≤ (111297179 / 200000000) := by
  have h := checkLog_sound (w := (953 / 3513)) (n := 12)
    (lo := (278242947 / 500000000)) (hi := (111297179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2233 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2233 / 1280) = 1/(1280 / 2233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (278242947 / 500000000) (111297179 / 200000000) (Real.log (2233 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2233 / 1280) = -Real.log (1280 / 2233) := by
    rw [show ((2233 / 1280) : ℝ) = ((1280 / 2233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (272931037 / 200000000) ≤ -Real.log (327 / 1280) ∧
    -Real.log (327 / 1280) ≤ (1364655187 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 967)) (n := 12)
    (lo := (134301601 / 200000000)) (hi := (335754003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 327) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 327) = 1/(327 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1364655187 / 1000000000) (-272931037 / 200000000) (Real.log (327 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (108393579 / 250000000) ≤ -Real.log (500000 / 771381) ∧
    -Real.log (500000 / 771381) ≤ (433574317 / 1000000000) := by
  have h := checkLog_sound (w := (271381 / 1271381)) (n := 12)
    (lo := (108393579 / 250000000)) (hi := (433574317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771381 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(771381 / 500000) = 1/(500000 / 771381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (108393579 / 250000000) (433574317 / 1000000000) (Real.log (771381 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (771381 / 500000) = -Real.log (500000 / 771381) := by
    rw [show ((771381 / 500000) : ℝ) = ((500000 / 771381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (156510247 / 200000000) ≤ -Real.log (228619 / 500000) ∧
    -Real.log (228619 / 500000) ≤ (782551237 / 1000000000) := by
  have h := checkLog_sound (w := (21381 / 478619)) (n := 12)
    (lo := (17880811 / 200000000)) (hi := (11175507 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228619) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 228619) = 1/(228619 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-782551237 / 1000000000) (-156510247 / 200000000) (Real.log (228619 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (13586709 / 31250000) ≤ -Real.log (200000 / 308923) ∧
    -Real.log (200000 / 308923) ≤ (434774689 / 1000000000) := by
  have h := checkLog_sound (w := (108923 / 508923)) (n := 12)
    (lo := (13586709 / 31250000)) (hi := (434774689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308923 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308923 / 200000) = 1/(200000 / 308923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (13586709 / 31250000) (434774689 / 1000000000) (Real.log (308923 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (308923 / 200000) = -Real.log (200000 / 308923) := by
    rw [show ((308923 / 200000) : ℝ) = ((200000 / 308923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (786612063 / 1000000000) ≤ -Real.log (91077 / 200000) ∧
    -Real.log (91077 / 200000) ≤ (157322413 / 200000000) := by
  have h := checkLog_sound (w := (8923 / 191077)) (n := 12)
    (lo := (93464883 / 1000000000)) (hi := (23366221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91077) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 91077) = 1/(91077 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-157322413 / 200000000) (-786612063 / 1000000000) (Real.log (91077 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (87255433 / 250000000) ≤ -Real.log (12500 / 17721) ∧
    -Real.log (12500 / 17721) ≤ (349021733 / 1000000000) := by
  have h := checkLog_sound (w := (5221 / 30221)) (n := 12)
    (lo := (87255433 / 250000000)) (hi := (349021733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17721 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17721 / 12500) = 1/(12500 / 17721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (87255433 / 250000000) (349021733 / 1000000000) (Real.log (17721 / 12500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (17721 / 12500) = -Real.log (12500 / 17721) := by
    rw [show ((17721 / 12500) : ℝ) = ((12500 / 17721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (270367577 / 500000000) ≤ -Real.log (7279 / 12500) ∧
    -Real.log (7279 / 12500) ≤ (108147031 / 200000000) := by
  have h := checkLog_sound (w := (5221 / 19779)) (n := 12)
    (lo := (270367577 / 500000000)) (hi := (108147031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 7279) = 1/(7279 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-108147031 / 200000000) (-270367577 / 500000000) (Real.log (7279 / 12500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21887747 / 62500000) ≤ -Real.log (1000000 / 1419357) ∧
    -Real.log (1000000 / 1419357) ≤ (350203953 / 1000000000) := by
  have h := checkLog_sound (w := (419357 / 2419357)) (n := 12)
    (lo := (21887747 / 62500000)) (hi := (350203953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1419357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1419357 / 1000000) = 1/(1000000 / 1419357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21887747 / 62500000) (350203953 / 1000000000) (Real.log (1419357 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1419357 / 1000000) = -Real.log (1000000 / 1419357) := by
    rw [show ((1419357 / 1000000) : ℝ) = ((1000000 / 1419357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16988099 / 31250000) ≤ -Real.log (580643 / 1000000) ∧
    -Real.log (580643 / 1000000) ≤ (543619169 / 1000000000) := by
  have h := checkLog_sound (w := (419357 / 1580643)) (n := 12)
    (lo := (16988099 / 31250000)) (hi := (543619169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 580643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 580643) = 1/(580643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-543619169 / 1000000000) (-16988099 / 31250000) (Real.log (580643 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1216125551 / 1000000000) ≤ -Real.log (31250000000 / 105440301331) ∧
    -Real.log (31250000000 / 105440301331) ≤ (1216125553 / 1000000000) := by
  have h := checkLog_sound (w := (42940301331 / 167940301331)) (n := 12)
    (lo := (522978371 / 1000000000)) (hi := (130744593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105440301331 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(105440301331 / 62500000000) = 1/(31250000000 / 105440301331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1216125551 / 1000000000) (1216125553 / 1000000000) (Real.log (105440301331 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (105440301331 / 31250000000) = -Real.log (31250000000 / 105440301331) := by
    rw [show ((105440301331 / 31250000000) : ℝ) = ((31250000000 / 105440301331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1221386751 / 1000000000) ≤ -Real.log (3906250000 / 13249563213) ∧
    -Real.log (3906250000 / 13249563213) ≤ (1221386753 / 1000000000) := by
  have h := checkLog_sound (w := (5437063213 / 21062063213)) (n := 12)
    (lo := (528239571 / 1000000000)) (hi := (132059893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13249563213 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(13249563213 / 7812500000) = 1/(3906250000 / 13249563213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1221386751 / 1000000000) (1221386753 / 1000000000) (Real.log (13249563213 / 3906250000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13249563213 / 3906250000) = -Real.log (3906250000 / 13249563213) := by
    rw [show ((13249563213 / 3906250000) : ℝ) = ((3906250000 / 13249563213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (444878443 / 500000000) ≤ -Real.log (125000000000 / 304317213903) ∧
    -Real.log (125000000000 / 304317213903) ≤ (111219611 / 125000000) := by
  have h := checkLog_sound (w := (54317213903 / 554317213903)) (n := 12)
    (lo := (98304853 / 500000000)) (hi := (196609707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304317213903 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(304317213903 / 250000000000) = 1/(125000000000 / 304317213903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (444878443 / 500000000) (111219611 / 125000000) (Real.log (304317213903 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (304317213903 / 125000000000) = -Real.log (125000000000 / 304317213903) := by
    rw [show ((304317213903 / 125000000000) : ℝ) = ((125000000000 / 304317213903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (11172789 / 12500000) ≤ -Real.log (25000000000 / 61111431637) ∧
    -Real.log (25000000000 / 61111431637) ≤ (446911561 / 500000000) := by
  have h := checkLog_sound (w := (11111431637 / 111111431637)) (n := 12)
    (lo := (10033797 / 50000000)) (hi := (200675941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61111431637 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(61111431637 / 50000000000) = 1/(25000000000 / 61111431637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (11172789 / 12500000) (446911561 / 500000000) (Real.log (61111431637 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (61111431637 / 25000000000) = -Real.log (25000000000 / 61111431637) := by
    rw [show ((61111431637 / 25000000000) : ℝ) = ((25000000000 / 61111431637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0119

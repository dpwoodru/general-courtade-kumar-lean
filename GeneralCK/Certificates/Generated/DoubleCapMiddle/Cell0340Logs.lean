import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0340
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

theorem reflection_log_1_neg : (107256331 / 500000000) ≤ -Real.log (1024 / 1269) ∧
    -Real.log (1024 / 1269) ≤ (214512663 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 2293)) (n := 12)
    (lo := (107256331 / 500000000)) (hi := (214512663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269 / 1024) = 1/(1024 / 1269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (107256331 / 500000000) (214512663 / 1000000000) (Real.log (1269 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1269 / 1024) = -Real.log (1024 / 1269) := by
    rw [show ((1269 / 1024) : ℝ) = ((1024 / 1269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (273460759 / 1000000000) ≤ -Real.log (779 / 1024) ∧
    -Real.log (779 / 1024) ≤ (6836519 / 25000000) := by
  have h := checkLog_sound (w := (245 / 1803)) (n := 12)
    (lo := (273460759 / 1000000000)) (hi := (6836519 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 779) = 1/(779 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6836519 / 25000000) (-273460759 / 1000000000) (Real.log (779 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (214276227 / 1000000000) ≤ -Real.log (10240 / 12687) ∧
    -Real.log (10240 / 12687) ≤ (53569057 / 250000000) := by
  have h := checkLog_sound (w := (2447 / 22927)) (n := 12)
    (lo := (214276227 / 1000000000)) (hi := (53569057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12687 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12687 / 10240) = 1/(10240 / 12687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (214276227 / 1000000000) (53569057 / 250000000) (Real.log (12687 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12687 / 10240) = -Real.log (10240 / 12687) := by
    rw [show ((12687 / 10240) : ℝ) = ((10240 / 12687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (68268931 / 250000000) ≤ -Real.log (7793 / 10240) ∧
    -Real.log (7793 / 10240) ≤ (10923029 / 40000000) := by
  have h := checkLog_sound (w := (2447 / 18033)) (n := 12)
    (lo := (68268931 / 250000000)) (hi := (10923029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7793) = 1/(7793 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10923029 / 40000000) (-68268931 / 250000000) (Real.log (7793 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (97759657 / 250000000) ≤ -Real.log (512 / 757) ∧
    -Real.log (512 / 757) ≤ (391038629 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 1269)) (n := 12)
    (lo := (97759657 / 250000000)) (hi := (391038629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757 / 512) = 1/(512 / 757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (97759657 / 250000000) (391038629 / 1000000000) (Real.log (757 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (757 / 512) = -Real.log (512 / 757) := by
    rw [show ((757 / 512) : ℝ) = ((512 / 757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (325537983 / 500000000) ≤ -Real.log (267 / 512) ∧
    -Real.log (267 / 512) ≤ (651075967 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 779)) (n := 12)
    (lo := (325537983 / 500000000)) (hi := (651075967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 267) = 1/(267 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-651075967 / 1000000000) (-325537983 / 500000000) (Real.log (267 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (48830281 / 125000000) ≤ -Real.log (5120 / 7567) ∧
    -Real.log (5120 / 7567) ≤ (390642249 / 1000000000) := by
  have h := checkLog_sound (w := (2447 / 12687)) (n := 12)
    (lo := (48830281 / 125000000)) (hi := (390642249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7567 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7567 / 5120) = 1/(5120 / 7567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (48830281 / 125000000) (390642249 / 1000000000) (Real.log (7567 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7567 / 5120) = -Real.log (5120 / 7567) := by
    rw [show ((7567 / 5120) : ℝ) = ((5120 / 7567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (649953001 / 1000000000) ≤ -Real.log (2673 / 5120) ∧
    -Real.log (2673 / 5120) ≤ (324976501 / 500000000) := by
  have h := checkLog_sound (w := (2447 / 7793)) (n := 12)
    (lo := (649953001 / 1000000000)) (hi := (324976501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2673) = 1/(2673 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-324976501 / 500000000) (-649953001 / 1000000000) (Real.log (2673 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29379659 / 100000000) ≤ -Real.log (1000000 / 1341511) ∧
    -Real.log (1000000 / 1341511) ≤ (293796591 / 1000000000) := by
  have h := checkLog_sound (w := (341511 / 2341511)) (n := 12)
    (lo := (29379659 / 100000000)) (hi := (293796591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341511 / 1000000) = 1/(1000000 / 1341511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29379659 / 100000000) (293796591 / 1000000000) (Real.log (1341511 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1341511 / 1000000) = -Real.log (1000000 / 1341511) := by
    rw [show ((1341511 / 1000000) : ℝ) = ((1000000 / 1341511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (208903731 / 500000000) ≤ -Real.log (658489 / 1000000) ∧
    -Real.log (658489 / 1000000) ≤ (417807463 / 1000000000) := by
  have h := checkLog_sound (w := (341511 / 1658489)) (n := 12)
    (lo := (208903731 / 500000000)) (hi := (417807463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 658489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 658489) = 1/(658489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-417807463 / 1000000000) (-208903731 / 500000000) (Real.log (658489 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (294117073 / 1000000000) ≤ -Real.log (1000000 / 1341941) ∧
    -Real.log (1000000 / 1341941) ≤ (147058537 / 500000000) := by
  have h := checkLog_sound (w := (341941 / 2341941)) (n := 12)
    (lo := (294117073 / 1000000000)) (hi := (147058537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341941 / 1000000) = 1/(1000000 / 1341941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (294117073 / 1000000000) (147058537 / 500000000) (Real.log (1341941 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1341941 / 1000000) = -Real.log (1000000 / 1341941) := by
    rw [show ((1341941 / 1000000) : ℝ) = ((1000000 / 1341941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (209230343 / 500000000) ≤ -Real.log (658059 / 1000000) ∧
    -Real.log (658059 / 1000000) ≤ (418460687 / 1000000000) := by
  have h := checkLog_sound (w := (341941 / 1658059)) (n := 12)
    (lo := (209230343 / 500000000)) (hi := (418460687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 658059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 658059) = 1/(658059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-418460687 / 1000000000) (-209230343 / 500000000) (Real.log (658059 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (222774683 / 1000000000) ≤ -Real.log (1000000 / 1249539) ∧
    -Real.log (1000000 / 1249539) ≤ (55693671 / 250000000) := by
  have h := checkLog_sound (w := (249539 / 2249539)) (n := 12)
    (lo := (222774683 / 1000000000)) (hi := (55693671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249539 / 1000000) = 1/(1000000 / 1249539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (222774683 / 1000000000) (55693671 / 250000000) (Real.log (1249539 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1249539 / 1000000) = -Real.log (1000000 / 1249539) := by
    rw [show ((1249539 / 1000000) : ℝ) = ((1000000 / 1249539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (143533797 / 500000000) ≤ -Real.log (750461 / 1000000) ∧
    -Real.log (750461 / 1000000) ≤ (57413519 / 200000000) := by
  have h := checkLog_sound (w := (249539 / 1750461)) (n := 12)
    (lo := (143533797 / 500000000)) (hi := (57413519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750461) = 1/(750461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-57413519 / 200000000) (-143533797 / 500000000) (Real.log (750461 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (111521373 / 500000000) ≤ -Real.log (500000 / 624937) ∧
    -Real.log (500000 / 624937) ≤ (223042747 / 1000000000) := by
  have h := checkLog_sound (w := (124937 / 1124937)) (n := 12)
    (lo := (111521373 / 500000000)) (hi := (223042747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624937 / 500000) = 1/(500000 / 624937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (111521373 / 500000000) (223042747 / 1000000000) (Real.log (624937 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (624937 / 500000) = -Real.log (500000 / 624937) := by
    rw [show ((624937 / 500000) : ℝ) = ((500000 / 624937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (143757043 / 500000000) ≤ -Real.log (375063 / 500000) ∧
    -Real.log (375063 / 500000) ≤ (287514087 / 1000000000) := by
  have h := checkLog_sound (w := (124937 / 875063)) (n := 12)
    (lo := (143757043 / 500000000)) (hi := (287514087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375063) = 1/(375063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-287514087 / 1000000000) (-143757043 / 500000000) (Real.log (375063 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (177901013 / 250000000) ≤ -Real.log (500000000000 / 1018628253471) ∧
    -Real.log (500000000000 / 1018628253471) ≤ (355802027 / 500000000) := by
  have h := checkLog_sound (w := (18628253471 / 2018628253471)) (n := 12)
    (lo := (2307109 / 125000000)) (hi := (18456873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1018628253471 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1018628253471 / 1000000000000) = 1/(500000000000 / 1018628253471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (177901013 / 250000000) (355802027 / 500000000) (Real.log (1018628253471 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1018628253471 / 500000000000) = -Real.log (500000000000 / 1018628253471) := by
    rw [show ((1018628253471 / 500000000000) : ℝ) = ((500000000000 / 1018628253471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (356288879 / 500000000) ≤ -Real.log (250000000000 / 509810290567) ∧
    -Real.log (250000000000 / 509810290567) ≤ (4453611 / 6250000) := by
  have h := checkLog_sound (w := (9810290567 / 1009810290567)) (n := 12)
    (lo := (9715289 / 500000000)) (hi := (19430579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((509810290567 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(509810290567 / 500000000000) = 1/(250000000000 / 509810290567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (356288879 / 500000000) (4453611 / 6250000) (Real.log (509810290567 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (509810290567 / 250000000000) = -Real.log (250000000000 / 509810290567) := by
    rw [show ((509810290567 / 250000000000) : ℝ) = ((250000000000 / 509810290567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (509842277 / 1000000000) ≤ -Real.log (500000000000 / 832514281221) ∧
    -Real.log (500000000000 / 832514281221) ≤ (254921139 / 500000000) := by
  have h := checkLog_sound (w := (332514281221 / 1332514281221)) (n := 12)
    (lo := (509842277 / 1000000000)) (hi := (254921139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((832514281221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(832514281221 / 500000000000) = 1/(500000000000 / 832514281221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (509842277 / 1000000000) (254921139 / 500000000) (Real.log (832514281221 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (832514281221 / 500000000000) = -Real.log (500000000000 / 832514281221) := by
    rw [show ((832514281221 / 500000000000) : ℝ) = ((500000000000 / 832514281221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (15954901 / 31250000) ≤ -Real.log (6250000000 / 10413867137) ∧
    -Real.log (6250000000 / 10413867137) ≤ (510556833 / 1000000000) := by
  have h := checkLog_sound (w := (4163867137 / 16663867137)) (n := 12)
    (lo := (15954901 / 31250000)) (hi := (510556833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10413867137 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10413867137 / 6250000000) = 1/(6250000000 / 10413867137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (15954901 / 31250000) (510556833 / 1000000000) (Real.log (10413867137 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10413867137 / 6250000000) = -Real.log (6250000000 / 10413867137) := by
    rw [show ((10413867137 / 6250000000) : ℝ) = ((6250000000 / 10413867137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0340

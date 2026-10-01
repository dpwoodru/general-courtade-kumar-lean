import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0438
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

theorem reflection_log_1_neg : (9553611 / 50000000) ≤ -Real.log (2560 / 3099) ∧
    -Real.log (2560 / 3099) ≤ (191072221 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 5659)) (n := 12)
    (lo := (9553611 / 50000000)) (hi := (191072221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3099 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3099 / 2560) = 1/(2560 / 3099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (9553611 / 50000000) (191072221 / 1000000000) (Real.log (3099 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3099 / 2560) = -Real.log (2560 / 3099) := by
    rw [show ((3099 / 2560) : ℝ) = ((2560 / 3099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (11820741 / 50000000) ≤ -Real.log (2021 / 2560) ∧
    -Real.log (2021 / 2560) ≤ (236414821 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 4581)) (n := 12)
    (lo := (11820741 / 50000000)) (hi := (236414821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2021) = 1/(2021 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-236414821 / 1000000000) (-11820741 / 50000000) (Real.log (2021 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (190830177 / 1000000000) ≤ -Real.log (10240 / 12393) ∧
    -Real.log (10240 / 12393) ≤ (95415089 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 22633)) (n := 12)
    (lo := (190830177 / 1000000000)) (hi := (95415089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12393 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12393 / 10240) = 1/(10240 / 12393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (190830177 / 1000000000) (95415089 / 500000000) (Real.log (12393 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12393 / 10240) = -Real.log (10240 / 12393) := by
    rw [show ((12393 / 10240) : ℝ) = ((10240 / 12393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (47208757 / 200000000) ≤ -Real.log (8087 / 10240) ∧
    -Real.log (8087 / 10240) ≤ (118021893 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 18327)) (n := 12)
    (lo := (47208757 / 200000000)) (hi := (118021893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8087) = 1/(8087 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-118021893 / 500000000) (-47208757 / 200000000) (Real.log (8087 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (351426821 / 1000000000) ≤ -Real.log (1280 / 1819) ∧
    -Real.log (1280 / 1819) ≤ (175713411 / 500000000) := by
  have h := checkLog_sound (w := (539 / 3099)) (n := 12)
    (lo := (351426821 / 1000000000)) (hi := (175713411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1819 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1819 / 1280) = 1/(1280 / 1819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (351426821 / 1000000000) (175713411 / 500000000) (Real.log (1819 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1819 / 1280) = -Real.log (1280 / 1819) := by
    rw [show ((1819 / 1280) : ℝ) = ((1280 / 1819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (546614731 / 1000000000) ≤ -Real.log (741 / 1280) ∧
    -Real.log (741 / 1280) ≤ (136653683 / 250000000) := by
  have h := checkLog_sound (w := (539 / 2021)) (n := 12)
    (lo := (546614731 / 1000000000)) (hi := (136653683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 741) = 1/(741 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-136653683 / 250000000) (-546614731 / 1000000000) (Real.log (741 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (175507211 / 500000000) ≤ -Real.log (5120 / 7273) ∧
    -Real.log (5120 / 7273) ≤ (351014423 / 1000000000) := by
  have h := checkLog_sound (w := (2153 / 12393)) (n := 12)
    (lo := (175507211 / 500000000)) (hi := (351014423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7273 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7273 / 5120) = 1/(5120 / 7273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (175507211 / 500000000) (351014423 / 1000000000) (Real.log (7273 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7273 / 5120) = -Real.log (5120 / 7273) := by
    rw [show ((7273 / 5120) : ℝ) = ((5120 / 7273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (545603097 / 1000000000) ≤ -Real.log (2967 / 5120) ∧
    -Real.log (2967 / 5120) ≤ (272801549 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 8087)) (n := 12)
    (lo := (545603097 / 1000000000)) (hi := (272801549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2967) = 1/(2967 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-272801549 / 500000000) (-545603097 / 1000000000) (Real.log (2967 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (262142701 / 1000000000) ≤ -Real.log (15625 / 20308) ∧
    -Real.log (15625 / 20308) ≤ (131071351 / 500000000) := by
  have h := checkLog_sound (w := (4683 / 35933)) (n := 12)
    (lo := (262142701 / 1000000000)) (hi := (131071351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20308 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20308 / 15625) = 1/(15625 / 20308) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (262142701 / 1000000000) (131071351 / 500000000) (Real.log (20308 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (20308 / 15625) = -Real.log (15625 / 20308) := by
    rw [show ((20308 / 15625) : ℝ) = ((15625 / 20308) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (356263599 / 1000000000) ≤ -Real.log (10942 / 15625) ∧
    -Real.log (10942 / 15625) ≤ (890659 / 2500000) := by
  have h := checkLog_sound (w := (4683 / 26567)) (n := 12)
    (lo := (356263599 / 1000000000)) (hi := (890659 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10942) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10942) = 1/(10942 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-890659 / 2500000) (-356263599 / 1000000000) (Real.log (10942 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (262469643 / 1000000000) ≤ -Real.log (1000000 / 1300137) ∧
    -Real.log (1000000 / 1300137) ≤ (65617411 / 250000000) := by
  have h := checkLog_sound (w := (300137 / 2300137)) (n := 12)
    (lo := (262469643 / 1000000000)) (hi := (65617411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1300137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1300137 / 1000000) = 1/(1000000 / 1300137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (262469643 / 1000000000) (65617411 / 250000000) (Real.log (1300137 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1300137 / 1000000) = -Real.log (1000000 / 1300137) := by
    rw [show ((1300137 / 1000000) : ℝ) = ((1000000 / 1300137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (356870677 / 1000000000) ≤ -Real.log (699863 / 1000000) ∧
    -Real.log (699863 / 1000000) ≤ (178435339 / 500000000) := by
  have h := checkLog_sound (w := (300137 / 1699863)) (n := 12)
    (lo := (356870677 / 1000000000)) (hi := (178435339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 699863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 699863) = 1/(699863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-178435339 / 500000000) (-356870677 / 1000000000) (Real.log (699863 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (61457 / 312500) ≤ -Real.log (1000000 / 1217333) ∧
    -Real.log (1000000 / 1217333) ≤ (196662401 / 1000000000) := by
  have h := checkLog_sound (w := (217333 / 2217333)) (n := 12)
    (lo := (61457 / 312500)) (hi := (196662401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217333 / 1000000) = 1/(1000000 / 1217333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (61457 / 312500) (196662401 / 1000000000) (Real.log (1217333 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1217333 / 1000000) = -Real.log (1000000 / 1217333) := by
    rw [show ((1217333 / 1000000) : ℝ) = ((1000000 / 1217333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (6126199 / 25000000) ≤ -Real.log (782667 / 1000000) ∧
    -Real.log (782667 / 1000000) ≤ (245047961 / 1000000000) := by
  have h := checkLog_sound (w := (217333 / 1782667)) (n := 12)
    (lo := (6126199 / 25000000)) (hi := (245047961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782667) = 1/(782667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-245047961 / 1000000000) (-6126199 / 25000000) (Real.log (782667 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (196929341 / 1000000000) ≤ -Real.log (500000 / 608829) ∧
    -Real.log (500000 / 608829) ≤ (98464671 / 500000000) := by
  have h := checkLog_sound (w := (108829 / 1108829)) (n := 12)
    (lo := (196929341 / 1000000000)) (hi := (98464671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608829 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608829 / 500000) = 1/(500000 / 608829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (196929341 / 1000000000) (98464671 / 500000000) (Real.log (608829 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (608829 / 500000) = -Real.log (500000 / 608829) := by
    rw [show ((608829 / 500000) : ℝ) = ((500000 / 608829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (245463293 / 1000000000) ≤ -Real.log (391171 / 500000) ∧
    -Real.log (391171 / 500000) ≤ (122731647 / 500000000) := by
  have h := checkLog_sound (w := (108829 / 891171)) (n := 12)
    (lo := (245463293 / 1000000000)) (hi := (122731647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391171) = 1/(391171 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-122731647 / 500000000) (-245463293 / 1000000000) (Real.log (391171 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (618406301 / 1000000000) ≤ -Real.log (500000000000 / 927983915189) ∧
    -Real.log (500000000000 / 927983915189) ≤ (309203151 / 500000000) := by
  have h := checkLog_sound (w := (427983915189 / 1427983915189)) (n := 12)
    (lo := (618406301 / 1000000000)) (hi := (309203151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927983915189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927983915189 / 500000000000) = 1/(500000000000 / 927983915189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (618406301 / 1000000000) (309203151 / 500000000) (Real.log (927983915189 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (927983915189 / 500000000000) = -Real.log (500000000000 / 927983915189) := by
    rw [show ((927983915189 / 500000000000) : ℝ) = ((500000000000 / 927983915189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3870877 / 6250000) ≤ -Real.log (500000000000 / 928851075139) ∧
    -Real.log (500000000000 / 928851075139) ≤ (619340321 / 1000000000) := by
  have h := checkLog_sound (w := (428851075139 / 1428851075139)) (n := 12)
    (lo := (3870877 / 6250000)) (hi := (619340321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((928851075139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(928851075139 / 500000000000) = 1/(500000000000 / 928851075139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3870877 / 6250000) (619340321 / 1000000000) (Real.log (928851075139 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (928851075139 / 500000000000) = -Real.log (500000000000 / 928851075139) := by
    rw [show ((928851075139 / 500000000000) : ℝ) = ((500000000000 / 928851075139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (441710361 / 1000000000) ≤ -Real.log (62500000000 / 97210323803) ∧
    -Real.log (62500000000 / 97210323803) ≤ (220855181 / 500000000) := by
  have h := checkLog_sound (w := (34710323803 / 159710323803)) (n := 12)
    (lo := (441710361 / 1000000000)) (hi := (220855181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97210323803 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97210323803 / 62500000000) = 1/(62500000000 / 97210323803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (441710361 / 1000000000) (220855181 / 500000000) (Real.log (97210323803 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (97210323803 / 62500000000) = -Real.log (62500000000 / 97210323803) := by
    rw [show ((97210323803 / 62500000000) : ℝ) = ((62500000000 / 97210323803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (88478527 / 200000000) ≤ -Real.log (62500000000 / 97276670561) ∧
    -Real.log (62500000000 / 97276670561) ≤ (110598159 / 250000000) := by
  have h := checkLog_sound (w := (34776670561 / 159776670561)) (n := 12)
    (lo := (88478527 / 200000000)) (hi := (110598159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97276670561 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97276670561 / 62500000000) = 1/(62500000000 / 97276670561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (88478527 / 200000000) (110598159 / 250000000) (Real.log (97276670561 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (97276670561 / 62500000000) = -Real.log (62500000000 / 97276670561) := by
    rw [show ((97276670561 / 62500000000) : ℝ) = ((62500000000 / 97276670561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0438

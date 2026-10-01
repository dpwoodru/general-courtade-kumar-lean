import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0219
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

theorem reflection_log_1_neg : (32136497 / 125000000) ≤ -Real.log (5120 / 6621) ∧
    -Real.log (5120 / 6621) ≤ (257091977 / 1000000000) := by
  have h := checkLog_sound (w := (1501 / 11741)) (n := 12)
    (lo := (32136497 / 125000000)) (hi := (257091977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6621 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6621 / 5120) = 1/(5120 / 6621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (32136497 / 125000000) (257091977 / 1000000000) (Real.log (6621 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6621 / 5120) = -Real.log (5120 / 6621) := by
    rw [show ((6621 / 5120) : ℝ) = ((5120 / 6621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (173478347 / 500000000) ≤ -Real.log (3619 / 5120) ∧
    -Real.log (3619 / 5120) ≤ (69391339 / 200000000) := by
  have h := checkLog_sound (w := (1501 / 8739)) (n := 12)
    (lo := (173478347 / 500000000)) (hi := (69391339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3619) = 1/(3619 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-69391339 / 200000000) (-173478347 / 500000000) (Real.log (3619 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (25663877 / 100000000) ≤ -Real.log (2560 / 3309) ∧
    -Real.log (2560 / 3309) ≤ (256638771 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 5869)) (n := 12)
    (lo := (25663877 / 100000000)) (hi := (256638771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3309 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3309 / 2560) = 1/(2560 / 3309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (25663877 / 100000000) (256638771 / 1000000000) (Real.log (3309 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3309 / 2560) = -Real.log (2560 / 3309) := by
    rw [show ((3309 / 2560) : ℝ) = ((2560 / 3309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (346128079 / 1000000000) ≤ -Real.log (1811 / 2560) ∧
    -Real.log (1811 / 2560) ≤ (4326601 / 12500000) := by
  have h := checkLog_sound (w := (749 / 4371)) (n := 12)
    (lo := (346128079 / 1000000000)) (hi := (4326601 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1811) = 1/(1811 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4326601 / 12500000) (-346128079 / 1000000000) (Real.log (1811 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (46142199 / 100000000) ≤ -Real.log (2560 / 4061) ∧
    -Real.log (2560 / 4061) ≤ (461421991 / 1000000000) := by
  have h := checkLog_sound (w := (1501 / 6621)) (n := 12)
    (lo := (46142199 / 100000000)) (hi := (461421991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4061 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4061 / 2560) = 1/(2560 / 4061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (46142199 / 100000000) (461421991 / 1000000000) (Real.log (4061 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4061 / 2560) = -Real.log (2560 / 4061) := by
    rw [show ((4061 / 2560) : ℝ) = ((2560 / 4061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (882682191 / 1000000000) ≤ -Real.log (1059 / 2560) ∧
    -Real.log (1059 / 2560) ≤ (882682193 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 2339)) (n := 12)
    (lo := (189535011 / 1000000000)) (hi := (47383753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1059) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1059) = 1/(1059 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-882682193 / 1000000000) (-882682191 / 1000000000) (Real.log (1059 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (230341491 / 500000000) ≤ -Real.log (1280 / 2029) ∧
    -Real.log (1280 / 2029) ≤ (460682983 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 3309)) (n := 12)
    (lo := (230341491 / 500000000)) (hi := (460682983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2029 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2029 / 1280) = 1/(1280 / 2029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (230341491 / 500000000) (460682983 / 1000000000) (Real.log (2029 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2029 / 1280) = -Real.log (1280 / 2029) := by
    rw [show ((2029 / 1280) : ℝ) = ((1280 / 2029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (175970667 / 200000000) ≤ -Real.log (531 / 1280) ∧
    -Real.log (531 / 1280) ≤ (879853337 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 1171)) (n := 12)
    (lo := (37341231 / 200000000)) (hi := (46676539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 531) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 531) = 1/(531 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-879853337 / 1000000000) (-175970667 / 200000000) (Real.log (531 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (175577669 / 500000000) ≤ -Real.log (250000 / 355177) ∧
    -Real.log (250000 / 355177) ≤ (351155339 / 1000000000) := by
  have h := checkLog_sound (w := (105177 / 605177)) (n := 12)
    (lo := (175577669 / 500000000)) (hi := (351155339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355177 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355177 / 250000) = 1/(250000 / 355177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (175577669 / 500000000) (351155339 / 1000000000) (Real.log (355177 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (355177 / 250000) = -Real.log (250000 / 355177) := by
    rw [show ((355177 / 250000) : ℝ) = ((250000 / 355177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (54594861 / 100000000) ≤ -Real.log (144823 / 250000) ∧
    -Real.log (144823 / 250000) ≤ (545948611 / 1000000000) := by
  have h := checkLog_sound (w := (105177 / 394823)) (n := 12)
    (lo := (54594861 / 100000000)) (hi := (545948611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 144823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 144823) = 1/(144823 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-545948611 / 1000000000) (-54594861 / 100000000) (Real.log (144823 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (175886223 / 500000000) ≤ -Real.log (200000 / 284317) ∧
    -Real.log (200000 / 284317) ≤ (351772447 / 1000000000) := by
  have h := checkLog_sound (w := (84317 / 484317)) (n := 12)
    (lo := (175886223 / 500000000)) (hi := (351772447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284317 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284317 / 200000) = 1/(200000 / 284317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (175886223 / 500000000) (351772447 / 1000000000) (Real.log (284317 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (284317 / 200000) = -Real.log (200000 / 284317) := by
    rw [show ((284317 / 200000) : ℝ) = ((200000 / 284317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (273731837 / 500000000) ≤ -Real.log (115683 / 200000) ∧
    -Real.log (115683 / 200000) ≤ (21898547 / 40000000) := by
  have h := checkLog_sound (w := (84317 / 315683)) (n := 12)
    (lo := (273731837 / 500000000)) (hi := (21898547 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 115683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 115683) = 1/(115683 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-21898547 / 40000000) (-273731837 / 500000000) (Real.log (115683 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (272150073 / 1000000000) ≤ -Real.log (62500 / 82049) ∧
    -Real.log (62500 / 82049) ≤ (136075037 / 500000000) := by
  have h := checkLog_sound (w := (19549 / 144549)) (n := 12)
    (lo := (272150073 / 1000000000)) (hi := (136075037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82049 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82049 / 62500) = 1/(62500 / 82049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (272150073 / 1000000000) (136075037 / 500000000) (Real.log (82049 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (82049 / 62500) = -Real.log (62500 / 82049) := by
    rw [show ((82049 / 62500) : ℝ) = ((62500 / 82049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3000853 / 8000000) ≤ -Real.log (42951 / 62500) ∧
    -Real.log (42951 / 62500) ≤ (187553313 / 500000000) := by
  have h := checkLog_sound (w := (19549 / 105451)) (n := 12)
    (lo := (3000853 / 8000000)) (hi := (187553313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42951) = 1/(42951 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-187553313 / 500000000) (-3000853 / 8000000) (Real.log (42951 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136348807 / 500000000) ≤ -Real.log (1000000 / 1313503) ∧
    -Real.log (1000000 / 1313503) ≤ (54539523 / 200000000) := by
  have h := checkLog_sound (w := (313503 / 2313503)) (n := 12)
    (lo := (136348807 / 500000000)) (hi := (54539523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313503 / 1000000) = 1/(1000000 / 1313503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136348807 / 500000000) (54539523 / 200000000) (Real.log (1313503 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1313503 / 1000000) = -Real.log (1000000 / 1313503) := by
    rw [show ((1313503 / 1000000) : ℝ) = ((1000000 / 1313503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (376153423 / 1000000000) ≤ -Real.log (686497 / 1000000) ∧
    -Real.log (686497 / 1000000) ≤ (23509589 / 62500000) := by
  have h := checkLog_sound (w := (313503 / 1686497)) (n := 12)
    (lo := (376153423 / 1000000000)) (hi := (23509589 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 686497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 686497) = 1/(686497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-23509589 / 62500000) (-376153423 / 1000000000) (Real.log (686497 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (897103949 / 1000000000) ≤ -Real.log (500000000000 / 1226245140619) ∧
    -Real.log (500000000000 / 1226245140619) ≤ (897103951 / 1000000000) := by
  have h := checkLog_sound (w := (226245140619 / 2226245140619)) (n := 12)
    (lo := (203956769 / 1000000000)) (hi := (20395677 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226245140619 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1226245140619 / 1000000000000) = 1/(500000000000 / 1226245140619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (897103949 / 1000000000) (897103951 / 1000000000) (Real.log (1226245140619 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1226245140619 / 500000000000) = -Real.log (500000000000 / 1226245140619) := by
    rw [show ((1226245140619 / 500000000000) : ℝ) = ((500000000000 / 1226245140619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (22480903 / 25000000) ≤ -Real.log (250000000000 / 614431247461) ∧
    -Real.log (250000000000 / 614431247461) ≤ (449618061 / 500000000) := by
  have h := checkLog_sound (w := (114431247461 / 1114431247461)) (n := 12)
    (lo := (10304447 / 50000000)) (hi := (206088941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614431247461 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(614431247461 / 500000000000) = 1/(250000000000 / 614431247461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (22480903 / 25000000) (449618061 / 500000000) (Real.log (614431247461 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (614431247461 / 250000000000) = -Real.log (250000000000 / 614431247461) := by
    rw [show ((614431247461 / 250000000000) : ℝ) = ((250000000000 / 614431247461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (323628349 / 500000000) ≤ -Real.log (500000000000 / 955146562361) ∧
    -Real.log (500000000000 / 955146562361) ≤ (647256699 / 1000000000) := by
  have h := checkLog_sound (w := (455146562361 / 1455146562361)) (n := 12)
    (lo := (323628349 / 500000000)) (hi := (647256699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955146562361 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955146562361 / 500000000000) = 1/(500000000000 / 955146562361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (323628349 / 500000000) (647256699 / 1000000000) (Real.log (955146562361 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (955146562361 / 500000000000) = -Real.log (500000000000 / 955146562361) := by
    rw [show ((955146562361 / 500000000000) : ℝ) = ((500000000000 / 955146562361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (648851037 / 1000000000) ≤ -Real.log (500000000000 / 956670604533) ∧
    -Real.log (500000000000 / 956670604533) ≤ (324425519 / 500000000) := by
  have h := checkLog_sound (w := (456670604533 / 1456670604533)) (n := 12)
    (lo := (648851037 / 1000000000)) (hi := (324425519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956670604533 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956670604533 / 500000000000) = 1/(500000000000 / 956670604533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (648851037 / 1000000000) (324425519 / 500000000) (Real.log (956670604533 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (956670604533 / 500000000000) = -Real.log (500000000000 / 956670604533) := by
    rw [show ((956670604533 / 500000000000) : ℝ) = ((500000000000 / 956670604533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0219

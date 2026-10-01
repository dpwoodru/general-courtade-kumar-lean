import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0221
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

theorem reflection_log_1_neg : (128092679 / 500000000) ≤ -Real.log (1024 / 1323) ∧
    -Real.log (1024 / 1323) ≤ (256185359 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2347)) (n := 12)
    (lo := (128092679 / 500000000)) (hi := (256185359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323 / 1024) = 1/(1024 / 1323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128092679 / 500000000) (256185359 / 1000000000) (Real.log (1323 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1323 / 1024) = -Real.log (1024 / 1323) := by
    rw [show ((1323 / 1024) : ℝ) = ((1024 / 1323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (6906003 / 20000000) ≤ -Real.log (725 / 1024) ∧
    -Real.log (725 / 1024) ≤ (345300151 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1749)) (n := 12)
    (lo := (6906003 / 20000000)) (hi := (345300151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 725) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 725) = 1/(725 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-345300151 / 1000000000) (-6906003 / 20000000) (Real.log (725 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12786587 / 50000000) ≤ -Real.log (1280 / 1653) ∧
    -Real.log (1280 / 1653) ≤ (255731741 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2933)) (n := 12)
    (lo := (12786587 / 50000000)) (hi := (255731741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653 / 1280) = 1/(1280 / 1653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12786587 / 50000000) (255731741 / 1000000000) (Real.log (1653 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1653 / 1280) = -Real.log (1280 / 1653) := by
    rw [show ((1653 / 1280) : ℝ) = ((1280 / 1653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (172236453 / 500000000) ≤ -Real.log (907 / 1280) ∧
    -Real.log (907 / 1280) ≤ (344472907 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2187)) (n := 12)
    (lo := (172236453 / 500000000)) (hi := (344472907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 907) = 1/(907 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-344472907 / 1000000000) (-172236453 / 500000000) (Real.log (907 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (459943429 / 1000000000) ≤ -Real.log (512 / 811) ∧
    -Real.log (512 / 811) ≤ (45994343 / 100000000) := by
  have h := checkLog_sound (w := (299 / 1323)) (n := 12)
    (lo := (459943429 / 1000000000)) (hi := (45994343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811 / 512) = 1/(512 / 811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (459943429 / 1000000000) (45994343 / 100000000) (Real.log (811 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (811 / 512) = -Real.log (512 / 811) := by
    rw [show ((811 / 512) : ℝ) = ((512 / 811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (438516229 / 500000000) ≤ -Real.log (213 / 512) ∧
    -Real.log (213 / 512) ≤ (43851623 / 50000000) := by
  have h := checkLog_sound (w := (43 / 469)) (n := 12)
    (lo := (91942639 / 500000000)) (hi := (183885279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 213) = 1/(213 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-43851623 / 50000000) (-438516229 / 500000000) (Real.log (213 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (459203327 / 1000000000) ≤ -Real.log (640 / 1013) ∧
    -Real.log (640 / 1013) ≤ (1793763 / 3906250) := by
  have h := checkLog_sound (w := (373 / 1653)) (n := 12)
    (lo := (459203327 / 1000000000)) (hi := (1793763 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1013 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1013 / 640) = 1/(640 / 1013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (459203327 / 1000000000) (1793763 / 3906250) (Real.log (1013 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1013 / 640) = -Real.log (640 / 1013) := by
    rw [show ((1013 / 640) : ℝ) = ((640 / 1013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (874219517 / 1000000000) ≤ -Real.log (267 / 640) ∧
    -Real.log (267 / 640) ≤ (874219519 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 587)) (n := 12)
    (lo := (181072337 / 1000000000)) (hi := (90536169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 267) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 267) = 1/(267 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-874219519 / 1000000000) (-874219517 / 1000000000) (Real.log (267 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (349922799 / 1000000000) ≤ -Real.log (500000 / 709479) ∧
    -Real.log (500000 / 709479) ≤ (874807 / 2500000) := by
  have h := checkLog_sound (w := (209479 / 1209479)) (n := 12)
    (lo := (349922799 / 1000000000)) (hi := (874807 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709479 / 500000) = 1/(500000 / 709479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (349922799 / 1000000000) (874807 / 2500000) (Real.log (709479 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (709479 / 500000) = -Real.log (500000 / 709479) := by
    rw [show ((709479 / 500000) : ℝ) = ((500000 / 709479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (108586447 / 200000000) ≤ -Real.log (290521 / 500000) ∧
    -Real.log (290521 / 500000) ≤ (135733059 / 250000000) := by
  have h := checkLog_sound (w := (209479 / 790521)) (n := 12)
    (lo := (108586447 / 200000000)) (hi := (135733059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 290521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 290521) = 1/(290521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-135733059 / 250000000) (-108586447 / 200000000) (Real.log (290521 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (350539963 / 1000000000) ≤ -Real.log (500000 / 709917) ∧
    -Real.log (500000 / 709917) ≤ (87634991 / 250000000) := by
  have h := checkLog_sound (w := (209917 / 1209917)) (n := 12)
    (lo := (350539963 / 1000000000)) (hi := (87634991 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709917 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709917 / 500000) = 1/(500000 / 709917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (350539963 / 1000000000) (87634991 / 250000000) (Real.log (709917 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (709917 / 500000) = -Real.log (500000 / 709917) := by
    rw [show ((709917 / 500000) : ℝ) = ((500000 / 709917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (544441009 / 1000000000) ≤ -Real.log (290083 / 500000) ∧
    -Real.log (290083 / 500000) ≤ (54444101 / 100000000) := by
  have h := checkLog_sound (w := (209917 / 790083)) (n := 12)
    (lo := (544441009 / 1000000000)) (hi := (54444101 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 290083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 290083) = 1/(290083 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-54444101 / 100000000) (-544441009 / 1000000000) (Real.log (290083 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13552857 / 50000000) ≤ -Real.log (20000 / 26227) ∧
    -Real.log (20000 / 26227) ≤ (271057141 / 1000000000) := by
  have h := checkLog_sound (w := (6227 / 46227)) (n := 12)
    (lo := (13552857 / 50000000)) (hi := (271057141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26227 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26227 / 20000) = 1/(20000 / 26227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13552857 / 50000000) (271057141 / 1000000000) (Real.log (26227 / 20000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (26227 / 20000) = -Real.log (20000 / 26227) := by
    rw [show ((26227 / 20000) : ℝ) = ((20000 / 26227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (373022119 / 1000000000) ≤ -Real.log (13773 / 20000) ∧
    -Real.log (13773 / 20000) ≤ (9325553 / 25000000) := by
  have h := checkLog_sound (w := (6227 / 33773)) (n := 12)
    (lo := (373022119 / 1000000000)) (hi := (9325553 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 13773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 13773) = 1/(13773 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-9325553 / 25000000) (-373022119 / 1000000000) (Real.log (13773 / 20000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (135802259 / 500000000) ≤ -Real.log (250000 / 328017) ∧
    -Real.log (250000 / 328017) ≤ (271604519 / 1000000000) := by
  have h := checkLog_sound (w := (78017 / 578017)) (n := 12)
    (lo := (135802259 / 500000000)) (hi := (271604519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328017 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328017 / 250000) = 1/(250000 / 328017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (135802259 / 500000000) (271604519 / 1000000000) (Real.log (328017 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (328017 / 250000) = -Real.log (250000 / 328017) := by
    rw [show ((328017 / 250000) : ℝ) = ((250000 / 328017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (374065283 / 1000000000) ≤ -Real.log (171983 / 250000) ∧
    -Real.log (171983 / 250000) ≤ (93516321 / 250000000) := by
  have h := checkLog_sound (w := (78017 / 421983)) (n := 12)
    (lo := (374065283 / 1000000000)) (hi := (93516321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171983) = 1/(171983 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-93516321 / 250000000) (-374065283 / 1000000000) (Real.log (171983 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (446427517 / 500000000) ≤ -Real.log (250000000000 / 610522991453) ∧
    -Real.log (250000000000 / 610522991453) ≤ (223213759 / 250000000) := by
  have h := checkLog_sound (w := (110522991453 / 1110522991453)) (n := 12)
    (lo := (99853927 / 500000000)) (hi := (39941571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610522991453 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(610522991453 / 500000000000) = 1/(250000000000 / 610522991453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (446427517 / 500000000) (223213759 / 250000000) (Real.log (610522991453 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (610522991453 / 250000000000) = -Real.log (250000000000 / 610522991453) := by
    rw [show ((610522991453 / 250000000000) : ℝ) = ((250000000000 / 610522991453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (223745243 / 250000000) ≤ -Real.log (25000000000 / 61182230603) ∧
    -Real.log (25000000000 / 61182230603) ≤ (447490487 / 500000000) := by
  have h := checkLog_sound (w := (11182230603 / 111182230603)) (n := 12)
    (lo := (3153653 / 15625000)) (hi := (201833793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61182230603 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(61182230603 / 50000000000) = 1/(25000000000 / 61182230603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (223745243 / 250000000) (447490487 / 500000000) (Real.log (61182230603 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (61182230603 / 25000000000) = -Real.log (25000000000 / 61182230603) := by
    rw [show ((61182230603 / 25000000000) : ℝ) = ((25000000000 / 61182230603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (32203963 / 50000000) ≤ -Real.log (25000000000 / 47605822987) ∧
    -Real.log (25000000000 / 47605822987) ≤ (644079261 / 1000000000) := by
  have h := checkLog_sound (w := (22605822987 / 72605822987)) (n := 12)
    (lo := (32203963 / 50000000)) (hi := (644079261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47605822987 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47605822987 / 25000000000) = 1/(25000000000 / 47605822987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (32203963 / 50000000) (644079261 / 1000000000) (Real.log (47605822987 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (47605822987 / 25000000000) = -Real.log (25000000000 / 47605822987) := by
    rw [show ((47605822987 / 25000000000) : ℝ) = ((25000000000 / 47605822987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (645669801 / 1000000000) ≤ -Real.log (125000000000 / 238408011257) ∧
    -Real.log (125000000000 / 238408011257) ≤ (322834901 / 500000000) := by
  have h := checkLog_sound (w := (113408011257 / 363408011257)) (n := 12)
    (lo := (645669801 / 1000000000)) (hi := (322834901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238408011257 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238408011257 / 125000000000) = 1/(125000000000 / 238408011257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (645669801 / 1000000000) (322834901 / 500000000) (Real.log (238408011257 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (238408011257 / 125000000000) = -Real.log (125000000000 / 238408011257) := by
    rw [show ((238408011257 / 125000000000) : ℝ) = ((125000000000 / 238408011257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0221

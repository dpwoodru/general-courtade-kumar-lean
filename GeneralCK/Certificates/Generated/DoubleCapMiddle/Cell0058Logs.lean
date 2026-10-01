import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0058
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

theorem reflection_log_1_neg : (184027627 / 500000000) ≤ -Real.log (2560 / 3699) ∧
    -Real.log (2560 / 3699) ≤ (73611051 / 200000000) := by
  have h := checkLog_sound (w := (1139 / 6259)) (n := 12)
    (lo := (184027627 / 500000000)) (hi := (73611051 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3699 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3699 / 2560) = 1/(2560 / 3699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (184027627 / 500000000) (73611051 / 200000000) (Real.log (3699 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3699 / 2560) = -Real.log (2560 / 3699) := by
    rw [show ((3699 / 2560) : ℝ) = ((2560 / 3699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (588646409 / 1000000000) ≤ -Real.log (1421 / 2560) ∧
    -Real.log (1421 / 2560) ≤ (58864641 / 100000000) := by
  have h := checkLog_sound (w := (1139 / 3981)) (n := 12)
    (lo := (588646409 / 1000000000)) (hi := (58864641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1421) = 1/(1421 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58864641 / 100000000) (-588646409 / 1000000000) (Real.log (1421 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (73448779 / 200000000) ≤ -Real.log (160 / 231) ∧
    -Real.log (160 / 231) ≤ (45905487 / 125000000) := by
  have h := checkLog_sound (w := (71 / 391)) (n := 12)
    (lo := (73448779 / 200000000)) (hi := (45905487 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231 / 160) = 1/(160 / 231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (73448779 / 200000000) (45905487 / 125000000) (Real.log (231 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (231 / 160) = -Real.log (160 / 231) := by
    rw [show ((231 / 160) : ℝ) = ((160 / 231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (117307489 / 200000000) ≤ -Real.log (89 / 160) ∧
    -Real.log (89 / 160) ≤ (293268723 / 500000000) := by
  have h := checkLog_sound (w := (71 / 249)) (n := 12)
    (lo := (117307489 / 200000000)) (hi := (293268723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 89) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 89) = 1/(89 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-293268723 / 500000000) (-117307489 / 200000000) (Real.log (89 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (636494153 / 1000000000) ≤ -Real.log (1280 / 2419) ∧
    -Real.log (1280 / 2419) ≤ (318247077 / 500000000) := by
  have h := checkLog_sound (w := (1139 / 3699)) (n := 12)
    (lo := (636494153 / 1000000000)) (hi := (318247077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2419 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2419 / 1280) = 1/(1280 / 2419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (636494153 / 1000000000) (318247077 / 500000000) (Real.log (2419 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2419 / 1280) = -Real.log (1280 / 2419) := by
    rw [show ((2419 / 1280) : ℝ) = ((1280 / 2419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (275731933 / 125000000) ≤ -Real.log (141 / 1280) ∧
    -Real.log (141 / 1280) ≤ (551463867 / 250000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 141) = 1/(141 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-551463867 / 250000000) (-275731933 / 125000000) (Real.log (141 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (317626601 / 500000000) ≤ -Real.log (80 / 151) ∧
    -Real.log (80 / 151) ≤ (635253203 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 231)) (n := 12)
    (lo := (317626601 / 500000000)) (hi := (635253203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151 / 80) = 1/(80 / 151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (317626601 / 500000000) (635253203 / 1000000000) (Real.log (151 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (151 / 80) = -Real.log (80 / 151) := by
    rw [show ((151 / 80) : ℝ) = ((80 / 151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (436960411 / 200000000) ≤ -Real.log (9 / 80) ∧
    -Real.log (9 / 80) ≤ (2184802059 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(10 / 9) = 1/(9 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2184802059 / 1000000000) (-436960411 / 200000000) (Real.log (9 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (253807437 / 500000000) ≤ -Real.log (250000 / 415331) ∧
    -Real.log (250000 / 415331) ≤ (4060919 / 8000000) := by
  have h := checkLog_sound (w := (165331 / 665331)) (n := 12)
    (lo := (253807437 / 500000000)) (hi := (4060919 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415331 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415331 / 250000) = 1/(250000 / 415331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (253807437 / 500000000) (4060919 / 8000000) (Real.log (415331 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (415331 / 250000) = -Real.log (250000 / 415331) := by
    rw [show ((415331 / 250000) : ℝ) = ((250000 / 415331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (54135569 / 50000000) ≤ -Real.log (84669 / 250000) ∧
    -Real.log (84669 / 250000) ≤ (541355691 / 500000000) := by
  have h := checkLog_sound (w := (40331 / 209669)) (n := 12)
    (lo := (1947821 / 5000000)) (hi := (389564201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84669) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 84669) = 1/(84669 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-541355691 / 500000000) (-54135569 / 50000000) (Real.log (84669 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (508867307 / 1000000000) ≤ -Real.log (500000 / 831703) ∧
    -Real.log (500000 / 831703) ≤ (127216827 / 250000000) := by
  have h := checkLog_sound (w := (331703 / 1331703)) (n := 12)
    (lo := (508867307 / 1000000000)) (hi := (127216827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831703 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831703 / 500000) = 1/(500000 / 831703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (508867307 / 1000000000) (127216827 / 250000000) (Real.log (831703 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (831703 / 500000) = -Real.log (500000 / 831703) := by
    rw [show ((831703 / 500000) : ℝ) = ((500000 / 831703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (544438911 / 500000000) ≤ -Real.log (168297 / 500000) ∧
    -Real.log (168297 / 500000) ≤ (4253429 / 3906250) := by
  have h := checkLog_sound (w := (81703 / 418297)) (n := 12)
    (lo := (197865321 / 500000000)) (hi := (395730643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 168297) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 168297) = 1/(168297 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4253429 / 3906250) (-544438911 / 500000000) (Real.log (168297 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (42607917 / 100000000) ≤ -Real.log (500000 / 765621) ∧
    -Real.log (500000 / 765621) ≤ (426079171 / 1000000000) := by
  have h := checkLog_sound (w := (265621 / 1265621)) (n := 12)
    (lo := (42607917 / 100000000)) (hi := (426079171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765621 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765621 / 500000) = 1/(500000 / 765621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (42607917 / 100000000) (426079171 / 1000000000) (Real.log (765621 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (765621 / 500000) = -Real.log (500000 / 765621) := by
    rw [show ((765621 / 500000) : ℝ) = ((500000 / 765621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (378834317 / 500000000) ≤ -Real.log (234379 / 500000) ∧
    -Real.log (234379 / 500000) ≤ (189417159 / 250000000) := by
  have h := checkLog_sound (w := (15621 / 484379)) (n := 12)
    (lo := (32260727 / 500000000)) (hi := (12904291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 234379) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 234379) = 1/(234379 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-189417159 / 250000000) (-378834317 / 500000000) (Real.log (234379 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (42746271 / 100000000) ≤ -Real.log (500000 / 766681) ∧
    -Real.log (500000 / 766681) ≤ (427462711 / 1000000000) := by
  have h := checkLog_sound (w := (266681 / 1266681)) (n := 12)
    (lo := (42746271 / 100000000)) (hi := (427462711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((766681 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(766681 / 500000) = 1/(500000 / 766681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (42746271 / 100000000) (427462711 / 1000000000) (Real.log (766681 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (766681 / 500000) = -Real.log (500000 / 766681) := by
    rw [show ((766681 / 500000) : ℝ) = ((500000 / 766681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (762201481 / 1000000000) ≤ -Real.log (233319 / 500000) ∧
    -Real.log (233319 / 500000) ≤ (762201483 / 1000000000) := by
  have h := checkLog_sound (w := (16681 / 483319)) (n := 12)
    (lo := (69054301 / 1000000000)) (hi := (34527151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 233319) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 233319) = 1/(233319 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-762201483 / 1000000000) (-762201481 / 1000000000) (Real.log (233319 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (795163127 / 500000000) ≤ -Real.log (500000000000 / 2452674532591) ∧
    -Real.log (500000000000 / 2452674532591) ≤ (1590326257 / 1000000000) := by
  have h := checkLog_sound (w := (452674532591 / 4452674532591)) (n := 12)
    (lo := (102015947 / 500000000)) (hi := (40806379 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2452674532591 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2452674532591 / 2000000000000) = 1/(500000000000 / 2452674532591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (795163127 / 500000000) (1590326257 / 1000000000) (Real.log (2452674532591 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2452674532591 / 500000000000) = -Real.log (500000000000 / 2452674532591) := by
    rw [show ((2452674532591 / 500000000000) : ℝ) = ((500000000000 / 2452674532591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1597745129 / 1000000000) ≤ -Real.log (500000000000 / 2470938281729) ∧
    -Real.log (500000000000 / 2470938281729) ≤ (399436283 / 250000000) := by
  have h := checkLog_sound (w := (470938281729 / 4470938281729)) (n := 12)
    (lo := (211450769 / 1000000000)) (hi := (21145077 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2470938281729 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2470938281729 / 2000000000000) = 1/(500000000000 / 2470938281729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1597745129 / 1000000000) (399436283 / 250000000) (Real.log (2470938281729 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2470938281729 / 500000000000) = -Real.log (500000000000 / 2470938281729) := by
    rw [show ((2470938281729 / 500000000000) : ℝ) = ((500000000000 / 2470938281729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (236749561 / 200000000) ≤ -Real.log (100000000000 / 326659385013) ∧
    -Real.log (100000000000 / 326659385013) ≤ (1183747807 / 1000000000) := by
  have h := checkLog_sound (w := (126659385013 / 526659385013)) (n := 12)
    (lo := (784961 / 1600000)) (hi := (245300313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326659385013 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(326659385013 / 200000000000) = 1/(100000000000 / 326659385013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (236749561 / 200000000) (1183747807 / 1000000000) (Real.log (326659385013 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (326659385013 / 100000000000) = -Real.log (100000000000 / 326659385013) := by
    rw [show ((326659385013 / 100000000000) : ℝ) = ((100000000000 / 326659385013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (18588503 / 15625000) ≤ -Real.log (500000000000 / 1642988783597) ∧
    -Real.log (500000000000 / 1642988783597) ≤ (594832097 / 500000000) := by
  have h := checkLog_sound (w := (642988783597 / 2642988783597)) (n := 12)
    (lo := (124129253 / 250000000)) (hi := (496517013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1642988783597 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1642988783597 / 1000000000000) = 1/(500000000000 / 1642988783597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (18588503 / 15625000) (594832097 / 500000000) (Real.log (1642988783597 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1642988783597 / 500000000000) = -Real.log (500000000000 / 1642988783597) := by
    rw [show ((1642988783597 / 500000000000) : ℝ) = ((500000000000 / 1642988783597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0058

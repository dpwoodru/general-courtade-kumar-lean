import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell194
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

theorem reflection_log_1_neg : (310610553 / 1000000000) ≤ -Real.log (1024 / 1397) ∧
    -Real.log (1024 / 1397) ≤ (155305277 / 500000000) := by
  have h := checkLog_sound (w := (373 / 2421)) (n := 12)
    (lo := (310610553 / 1000000000)) (hi := (155305277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397 / 1024) = 1/(1024 / 1397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (310610553 / 1000000000) (155305277 / 500000000) (Real.log (1397 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1397 / 1024) = -Real.log (1024 / 1397) := by
    rw [show ((1397 / 1024) : ℝ) = ((1024 / 1397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (452962163 / 1000000000) ≤ -Real.log (651 / 1024) ∧
    -Real.log (651 / 1024) ≤ (113240541 / 250000000) := by
  have h := checkLog_sound (w := (373 / 1675)) (n := 12)
    (lo := (452962163 / 1000000000)) (hi := (113240541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 651) = 1/(651 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-113240541 / 250000000) (-452962163 / 1000000000) (Real.log (651 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (310180969 / 1000000000) ≤ -Real.log (2560 / 3491) ∧
    -Real.log (2560 / 3491) ≤ (31018097 / 100000000) := by
  have h := checkLog_sound (w := (931 / 6051)) (n := 12)
    (lo := (310180969 / 1000000000)) (hi := (31018097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3491 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3491 / 2560) = 1/(2560 / 3491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (310180969 / 1000000000) (31018097 / 100000000) (Real.log (3491 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3491 / 2560) = -Real.log (2560 / 3491) := by
    rw [show ((3491 / 2560) : ℝ) = ((2560 / 3491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (14126279 / 31250000) ≤ -Real.log (1629 / 2560) ∧
    -Real.log (1629 / 2560) ≤ (452040929 / 1000000000) := by
  have h := checkLog_sound (w := (931 / 4189)) (n := 12)
    (lo := (14126279 / 31250000)) (hi := (452040929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1629) = 1/(1629 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-452040929 / 1000000000) (-14126279 / 31250000) (Real.log (1629 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23004369 / 100000000) ≤ -Real.log (200000 / 251731) ∧
    -Real.log (200000 / 251731) ≤ (230043691 / 1000000000) := by
  have h := checkLog_sound (w := (51731 / 451731)) (n := 12)
    (lo := (23004369 / 100000000)) (hi := (230043691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251731 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251731 / 200000) = 1/(200000 / 251731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23004369 / 100000000) (230043691 / 1000000000) (Real.log (251731 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (251731 / 200000) = -Real.log (200000 / 251731) := by
    rw [show ((251731 / 200000) : ℝ) = ((200000 / 251731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (149644587 / 500000000) ≤ -Real.log (148269 / 200000) ∧
    -Real.log (148269 / 200000) ≤ (11971567 / 40000000) := by
  have h := checkLog_sound (w := (51731 / 348269)) (n := 12)
    (lo := (149644587 / 500000000)) (hi := (11971567 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148269) = 1/(148269 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11971567 / 40000000) (-149644587 / 500000000) (Real.log (148269 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (230379707 / 1000000000) ≤ -Real.log (500000 / 629539) ∧
    -Real.log (500000 / 629539) ≤ (57594927 / 250000000) := by
  have h := checkLog_sound (w := (129539 / 1129539)) (n := 12)
    (lo := (230379707 / 1000000000)) (hi := (57594927 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629539 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629539 / 500000) = 1/(500000 / 629539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (230379707 / 1000000000) (57594927 / 250000000) (Real.log (629539 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (629539 / 500000) = -Real.log (500000 / 629539) := by
    rw [show ((629539 / 500000) : ℝ) = ((500000 / 629539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (149929961 / 500000000) ≤ -Real.log (370461 / 500000) ∧
    -Real.log (370461 / 500000) ≤ (299859923 / 1000000000) := by
  have h := checkLog_sound (w := (129539 / 870461)) (n := 12)
    (lo := (149929961 / 500000000)) (hi := (299859923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 370461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 370461) = 1/(370461 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-299859923 / 1000000000) (-149929961 / 500000000) (Real.log (370461 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85440683 / 500000000) ≤ -Real.log (20000 / 23727) ∧
    -Real.log (20000 / 23727) ≤ (170881367 / 1000000000) := by
  have h := checkLog_sound (w := (3727 / 43727)) (n := 12)
    (lo := (85440683 / 500000000)) (hi := (170881367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23727 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23727 / 20000) = 1/(20000 / 23727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85440683 / 500000000) (170881367 / 1000000000) (Real.log (23727 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (23727 / 20000) = -Real.log (20000 / 23727) := by
    rw [show ((23727 / 20000) : ℝ) = ((20000 / 23727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10311249 / 50000000) ≤ -Real.log (16273 / 20000) ∧
    -Real.log (16273 / 20000) ≤ (206224981 / 1000000000) := by
  have h := checkLog_sound (w := (3727 / 36273)) (n := 12)
    (lo := (10311249 / 50000000)) (hi := (206224981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 16273) = 1/(16273 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-206224981 / 1000000000) (-10311249 / 50000000) (Real.log (16273 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (171148537 / 1000000000) ≤ -Real.log (1000000 / 1186667) ∧
    -Real.log (1000000 / 1186667) ≤ (85574269 / 500000000) := by
  have h := checkLog_sound (w := (186667 / 2186667)) (n := 12)
    (lo := (171148537 / 1000000000)) (hi := (85574269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186667 / 1000000) = 1/(1000000 / 1186667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (171148537 / 1000000000) (85574269 / 500000000) (Real.log (1186667 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1186667 / 1000000) = -Real.log (1000000 / 1186667) := by
    rw [show ((1186667 / 1000000) : ℝ) = ((1000000 / 1186667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (206614659 / 1000000000) ≤ -Real.log (813333 / 1000000) ∧
    -Real.log (813333 / 1000000) ≤ (10330733 / 50000000) := by
  have h := checkLog_sound (w := (186667 / 1813333)) (n := 12)
    (lo := (206614659 / 1000000000)) (hi := (10330733 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813333) = 1/(813333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-10330733 / 50000000) (-206614659 / 1000000000) (Real.log (813333 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (762221897 / 1000000000) ≤ -Real.log (3906250000 / 8371220841) ∧
    -Real.log (3906250000 / 8371220841) ≤ (762221899 / 1000000000) := by
  have h := checkLog_sound (w := (558720841 / 16183720841)) (n := 12)
    (lo := (69074717 / 1000000000)) (hi := (34537359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8371220841 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8371220841 / 7812500000) = 1/(3906250000 / 8371220841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (762221897 / 1000000000) (762221899 / 1000000000) (Real.log (8371220841 / 3906250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (8371220841 / 3906250000) = -Real.log (3906250000 / 8371220841) := by
    rw [show ((8371220841 / 3906250000) : ℝ) = ((3906250000 / 8371220841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (190893179 / 250000000) ≤ -Real.log (500000000000 / 1072964669739) ∧
    -Real.log (500000000000 / 1072964669739) ≤ (381786359 / 500000000) := by
  have h := checkLog_sound (w := (72964669739 / 2072964669739)) (n := 12)
    (lo := (1100399 / 15625000)) (hi := (70425537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1072964669739 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1072964669739 / 1000000000000) = 1/(500000000000 / 1072964669739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (190893179 / 250000000) (381786359 / 500000000) (Real.log (1072964669739 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1072964669739 / 500000000000) = -Real.log (500000000000 / 1072964669739) := by
    rw [show ((1072964669739 / 500000000000) : ℝ) = ((500000000000 / 1072964669739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (105866573 / 200000000) ≤ -Real.log (250000000000 / 424449817561) ∧
    -Real.log (250000000000 / 424449817561) ≤ (264666433 / 500000000) := by
  have h := checkLog_sound (w := (174449817561 / 674449817561)) (n := 12)
    (lo := (105866573 / 200000000)) (hi := (264666433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424449817561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424449817561 / 250000000000) = 1/(250000000000 / 424449817561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (105866573 / 200000000) (264666433 / 500000000) (Real.log (424449817561 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (424449817561 / 250000000000) = -Real.log (250000000000 / 424449817561) := by
    rw [show ((424449817561 / 250000000000) : ℝ) = ((250000000000 / 424449817561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (530239629 / 1000000000) ≤ -Real.log (62500000000 / 106208716977) ∧
    -Real.log (62500000000 / 106208716977) ≤ (53023963 / 100000000) := by
  have h := checkLog_sound (w := (43708716977 / 168708716977)) (n := 12)
    (lo := (530239629 / 1000000000)) (hi := (53023963 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106208716977 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106208716977 / 62500000000) = 1/(62500000000 / 106208716977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (530239629 / 1000000000) (53023963 / 100000000) (Real.log (106208716977 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (106208716977 / 62500000000) = -Real.log (62500000000 / 106208716977) := by
    rw [show ((106208716977 / 62500000000) : ℝ) = ((62500000000 / 106208716977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (377106347 / 1000000000) ≤ -Real.log (250000000000 / 364514840533) ∧
    -Real.log (250000000000 / 364514840533) ≤ (94276587 / 250000000) := by
  have h := checkLog_sound (w := (114514840533 / 614514840533)) (n := 12)
    (lo := (377106347 / 1000000000)) (hi := (94276587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364514840533 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364514840533 / 250000000000) = 1/(250000000000 / 364514840533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (377106347 / 1000000000) (94276587 / 250000000) (Real.log (364514840533 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (364514840533 / 250000000000) = -Real.log (250000000000 / 364514840533) := by
    rw [show ((364514840533 / 250000000000) : ℝ) = ((250000000000 / 364514840533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (94440799 / 250000000) ≤ -Real.log (500000000000 / 729508700619) ∧
    -Real.log (500000000000 / 729508700619) ≤ (377763197 / 1000000000) := by
  have h := checkLog_sound (w := (229508700619 / 1229508700619)) (n := 12)
    (lo := (94440799 / 250000000)) (hi := (377763197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729508700619 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729508700619 / 500000000000) = 1/(500000000000 / 729508700619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (94440799 / 250000000) (377763197 / 1000000000) (Real.log (729508700619 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (729508700619 / 500000000000) = -Real.log (500000000000 / 729508700619) := by
    rw [show ((729508700619 / 500000000000) : ℝ) = ((500000000000 / 729508700619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17733061 / 500000000) ≤ -Real.log (965155431111 / 1000000000000) ∧
    -Real.log (965155431111 / 1000000000000) ≤ (35466123 / 1000000000) := by
  have h := checkLog_sound (w := (34844568889 / 1965155431111)) (n := 12)
    (lo := (17733061 / 500000000)) (hi := (35466123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965155431111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965155431111) = 1/(965155431111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-35466123 / 1000000000) (-17733061 / 500000000) (Real.log (965155431111 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17671807 / 500000000) ≤ -Real.log (386109471 / 400000000) ∧
    -Real.log (386109471 / 400000000) ≤ (7068723 / 200000000) := by
  have h := checkLog_sound (w := (13890529 / 786109471)) (n := 12)
    (lo := (17671807 / 500000000)) (hi := (7068723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 386109471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 386109471) = 1/(386109471 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7068723 / 200000000) (-17671807 / 500000000) (Real.log (386109471 / 400000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell194

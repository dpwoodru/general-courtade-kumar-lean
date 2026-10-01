import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0325
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

theorem reflection_log_1_neg : (27256561 / 125000000) ≤ -Real.log (2048 / 2547) ∧
    -Real.log (2048 / 2547) ≤ (218052489 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 4595)) (n := 12)
    (lo := (27256561 / 125000000)) (hi := (218052489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2547 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2547 / 2048) = 1/(2048 / 2547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27256561 / 125000000) (218052489 / 1000000000) (Real.log (2547 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2547 / 2048) = -Real.log (2048 / 2547) := by
    rw [show ((2547 / 2048) : ℝ) = ((2048 / 2547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (55850829 / 200000000) ≤ -Real.log (1549 / 2048) ∧
    -Real.log (1549 / 2048) ≤ (139627073 / 500000000) := by
  have h := checkLog_sound (w := (499 / 3597)) (n := 12)
    (lo := (55850829 / 200000000)) (hi := (139627073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1549) = 1/(1549 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-139627073 / 500000000) (-55850829 / 200000000) (Real.log (1549 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (217816889 / 1000000000) ≤ -Real.log (2560 / 3183) ∧
    -Real.log (2560 / 3183) ≤ (21781689 / 100000000) := by
  have h := checkLog_sound (w := (623 / 5743)) (n := 12)
    (lo := (217816889 / 1000000000)) (hi := (21781689 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3183 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3183 / 2560) = 1/(2560 / 3183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (217816889 / 1000000000) (21781689 / 100000000) (Real.log (3183 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3183 / 2560) = -Real.log (2560 / 3183) := by
    rw [show ((3183 / 2560) : ℝ) = ((2560 / 3183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (139433437 / 500000000) ≤ -Real.log (1937 / 2560) ∧
    -Real.log (1937 / 2560) ≤ (446187 / 1600000) := by
  have h := checkLog_sound (w := (623 / 4497)) (n := 12)
    (lo := (139433437 / 500000000)) (hi := (446187 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1937) = 1/(1937 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-446187 / 1600000) (-139433437 / 500000000) (Real.log (1937 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (396965547 / 1000000000) ≤ -Real.log (1024 / 1523) ∧
    -Real.log (1024 / 1523) ≤ (99241387 / 250000000) := by
  have h := checkLog_sound (w := (499 / 2547)) (n := 12)
    (lo := (396965547 / 1000000000)) (hi := (99241387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1523 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1523 / 1024) = 1/(1024 / 1523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (396965547 / 1000000000) (99241387 / 250000000) (Real.log (1523 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1523 / 1024) = -Real.log (1024 / 1523) := by
    rw [show ((1523 / 1024) : ℝ) = ((1024 / 1523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (668073543 / 1000000000) ≤ -Real.log (525 / 1024) ∧
    -Real.log (525 / 1024) ≤ (83509193 / 125000000) := by
  have h := checkLog_sound (w := (499 / 1549)) (n := 12)
    (lo := (668073543 / 1000000000)) (hi := (83509193 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 525) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 525) = 1/(525 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-83509193 / 125000000) (-668073543 / 1000000000) (Real.log (525 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (39657151 / 100000000) ≤ -Real.log (1280 / 1903) ∧
    -Real.log (1280 / 1903) ≤ (396571511 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 3183)) (n := 12)
    (lo := (39657151 / 100000000)) (hi := (396571511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1903 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1903 / 1280) = 1/(1280 / 1903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (39657151 / 100000000) (396571511 / 1000000000) (Real.log (1903 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1903 / 1280) = -Real.log (1280 / 1903) := by
    rw [show ((1903 / 1280) : ℝ) = ((1280 / 1903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (333465669 / 500000000) ≤ -Real.log (657 / 1280) ∧
    -Real.log (657 / 1280) ≤ (666931339 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 1937)) (n := 12)
    (lo := (333465669 / 500000000)) (hi := (666931339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 657) = 1/(657 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-666931339 / 1000000000) (-333465669 / 500000000) (Real.log (657 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (37322373 / 125000000) ≤ -Real.log (500000 / 673971) ∧
    -Real.log (500000 / 673971) ≤ (59715797 / 200000000) := by
  have h := checkLog_sound (w := (173971 / 1173971)) (n := 12)
    (lo := (37322373 / 125000000)) (hi := (59715797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673971 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673971 / 500000) = 1/(500000 / 673971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (37322373 / 125000000) (59715797 / 200000000) (Real.log (673971 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (673971 / 500000) = -Real.log (500000 / 673971) := by
    rw [show ((673971 / 500000) : ℝ) = ((500000 / 673971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (427621763 / 1000000000) ≤ -Real.log (326029 / 500000) ∧
    -Real.log (326029 / 500000) ≤ (106905441 / 250000000) := by
  have h := checkLog_sound (w := (173971 / 826029)) (n := 12)
    (lo := (427621763 / 1000000000)) (hi := (106905441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 326029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 326029) = 1/(326029 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-106905441 / 250000000) (-427621763 / 1000000000) (Real.log (326029 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (149448969 / 500000000) ≤ -Real.log (250000 / 337093) ∧
    -Real.log (250000 / 337093) ≤ (298897939 / 1000000000) := by
  have h := checkLog_sound (w := (87093 / 587093)) (n := 12)
    (lo := (149448969 / 500000000)) (hi := (298897939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337093 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(337093 / 250000) = 1/(250000 / 337093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (149448969 / 500000000) (298897939 / 1000000000) (Real.log (337093 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (337093 / 250000) = -Real.log (250000 / 337093) := by
    rw [show ((337093 / 250000) : ℝ) = ((250000 / 337093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53535179 / 125000000) ≤ -Real.log (162907 / 250000) ∧
    -Real.log (162907 / 250000) ≤ (428281433 / 1000000000) := by
  have h := checkLog_sound (w := (87093 / 412907)) (n := 12)
    (lo := (53535179 / 125000000)) (hi := (428281433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 162907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 162907) = 1/(162907 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-428281433 / 1000000000) (-53535179 / 125000000) (Real.log (162907 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (56696029 / 250000000) ≤ -Real.log (1000000 / 1254559) ∧
    -Real.log (1000000 / 1254559) ≤ (226784117 / 1000000000) := by
  have h := checkLog_sound (w := (254559 / 2254559)) (n := 12)
    (lo := (56696029 / 250000000)) (hi := (226784117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254559 / 1000000) = 1/(1000000 / 1254559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (56696029 / 250000000) (226784117 / 1000000000) (Real.log (1254559 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1254559 / 1000000) = -Real.log (1000000 / 1254559) := by
    rw [show ((1254559 / 1000000) : ℝ) = ((1000000 / 1254559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (293779289 / 1000000000) ≤ -Real.log (745441 / 1000000) ∧
    -Real.log (745441 / 1000000) ≤ (29377929 / 100000000) := by
  have h := checkLog_sound (w := (254559 / 1745441)) (n := 12)
    (lo := (293779289 / 1000000000)) (hi := (29377929 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745441) = 1/(745441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-29377929 / 100000000) (-293779289 / 1000000000) (Real.log (745441 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (2270527 / 10000000) ≤ -Real.log (62500 / 78431) ∧
    -Real.log (62500 / 78431) ≤ (227052701 / 1000000000) := by
  have h := checkLog_sound (w := (15931 / 140931)) (n := 12)
    (lo := (2270527 / 10000000)) (hi := (227052701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78431 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78431 / 62500) = 1/(62500 / 78431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (2270527 / 10000000) (227052701 / 1000000000) (Real.log (78431 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (78431 / 62500) = -Real.log (62500 / 78431) := by
    rw [show ((78431 / 62500) : ℝ) = ((62500 / 78431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (294231473 / 1000000000) ≤ -Real.log (46569 / 62500) ∧
    -Real.log (46569 / 62500) ≤ (147115737 / 500000000) := by
  have h := checkLog_sound (w := (15931 / 109069)) (n := 12)
    (lo := (294231473 / 1000000000)) (hi := (147115737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46569) = 1/(46569 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-147115737 / 500000000) (-294231473 / 1000000000) (Real.log (46569 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (181550187 / 250000000) ≤ -Real.log (500000000000 / 1033605906223) ∧
    -Real.log (500000000000 / 1033605906223) ≤ (2904803 / 4000000) := by
  have h := checkLog_sound (w := (33605906223 / 2033605906223)) (n := 12)
    (lo := (258231 / 7812500)) (hi := (33053569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1033605906223 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1033605906223 / 1000000000000) = 1/(500000000000 / 1033605906223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (181550187 / 250000000) (2904803 / 4000000) (Real.log (1033605906223 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1033605906223 / 500000000000) = -Real.log (500000000000 / 1033605906223) := by
    rw [show ((1033605906223 / 500000000000) : ℝ) = ((500000000000 / 1033605906223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (72717937 / 100000000) ≤ -Real.log (500000000000 / 1034617910833) ∧
    -Real.log (500000000000 / 1034617910833) ≤ (181794843 / 250000000) := by
  have h := checkLog_sound (w := (34617910833 / 2034617910833)) (n := 12)
    (lo := (3403219 / 100000000)) (hi := (34032191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1034617910833 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1034617910833 / 1000000000000) = 1/(500000000000 / 1034617910833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (72717937 / 100000000) (181794843 / 250000000) (Real.log (1034617910833 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1034617910833 / 500000000000) = -Real.log (500000000000 / 1034617910833) := by
    rw [show ((1034617910833 / 500000000000) : ℝ) = ((500000000000 / 1034617910833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (104112681 / 200000000) ≤ -Real.log (31250000000 / 52592986903) ∧
    -Real.log (31250000000 / 52592986903) ≤ (260281703 / 500000000) := by
  have h := checkLog_sound (w := (21342986903 / 83842986903)) (n := 12)
    (lo := (104112681 / 200000000)) (hi := (260281703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52592986903 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52592986903 / 31250000000) = 1/(31250000000 / 52592986903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (104112681 / 200000000) (260281703 / 500000000) (Real.log (52592986903 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (52592986903 / 31250000000) = -Real.log (31250000000 / 52592986903) := by
    rw [show ((52592986903 / 31250000000) : ℝ) = ((31250000000 / 52592986903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (521284173 / 1000000000) ≤ -Real.log (250000000000 / 421047263201) ∧
    -Real.log (250000000000 / 421047263201) ≤ (260642087 / 500000000) := by
  have h := checkLog_sound (w := (171047263201 / 671047263201)) (n := 12)
    (lo := (521284173 / 1000000000)) (hi := (260642087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421047263201 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421047263201 / 250000000000) = 1/(250000000000 / 421047263201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (521284173 / 1000000000) (260642087 / 500000000) (Real.log (421047263201 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (421047263201 / 250000000000) = -Real.log (250000000000 / 421047263201) := by
    rw [show ((421047263201 / 250000000000) : ℝ) = ((250000000000 / 421047263201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0325

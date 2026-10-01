import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell025
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

theorem reflection_log_1_neg : (235257381 / 1000000000) ≤ -Real.log (2560 / 3239) ∧
    -Real.log (2560 / 3239) ≤ (117628691 / 500000000) := by
  have h := checkLog_sound (w := (679 / 5799)) (n := 12)
    (lo := (235257381 / 1000000000)) (hi := (117628691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3239 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3239 / 2560) = 1/(2560 / 3239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (235257381 / 1000000000) (117628691 / 500000000) (Real.log (3239 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3239 / 2560) = -Real.log (2560 / 3239) := by
    rw [show ((3239 / 2560) : ℝ) = ((2560 / 3239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (77050927 / 250000000) ≤ -Real.log (1881 / 2560) ∧
    -Real.log (1881 / 2560) ≤ (308203709 / 1000000000) := by
  have h := checkLog_sound (w := (679 / 4441)) (n := 12)
    (lo := (77050927 / 250000000)) (hi := (308203709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1881) = 1/(1881 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-308203709 / 1000000000) (-77050927 / 250000000) (Real.log (1881 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (29349271 / 125000000) ≤ -Real.log (1024 / 1295) ∧
    -Real.log (1024 / 1295) ≤ (234794169 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2319)) (n := 12)
    (lo := (29349271 / 125000000)) (hi := (234794169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295 / 1024) = 1/(1024 / 1295) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (29349271 / 125000000) (234794169 / 1000000000) (Real.log (1295 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1295 / 1024) = -Real.log (1024 / 1295) := by
    rw [show ((1295 / 1024) : ℝ) = ((1024 / 1295) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (307406577 / 1000000000) ≤ -Real.log (753 / 1024) ∧
    -Real.log (753 / 1024) ≤ (153703289 / 500000000) := by
  have h := checkLog_sound (w := (271 / 1777)) (n := 12)
    (lo := (307406577 / 1000000000)) (hi := (153703289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 753) = 1/(753 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-153703289 / 500000000) (-307406577 / 1000000000) (Real.log (753 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (172016137 / 1000000000) ≤ -Real.log (1000000 / 1187697) ∧
    -Real.log (1000000 / 1187697) ≤ (86008069 / 500000000) := by
  have h := checkLog_sound (w := (187697 / 2187697)) (n := 12)
    (lo := (172016137 / 1000000000)) (hi := (86008069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187697 / 1000000) = 1/(1000000 / 1187697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (172016137 / 1000000000) (86008069 / 500000000) (Real.log (1187697 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1187697 / 1000000) = -Real.log (1000000 / 1187697) := by
    rw [show ((1187697 / 1000000) : ℝ) = ((1000000 / 1187697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (41576371 / 200000000) ≤ -Real.log (812303 / 1000000) ∧
    -Real.log (812303 / 1000000) ≤ (1624077 / 7812500) := by
  have h := checkLog_sound (w := (187697 / 1812303)) (n := 12)
    (lo := (41576371 / 200000000)) (hi := (1624077 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 812303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 812303) = 1/(812303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1624077 / 7812500) (-41576371 / 200000000) (Real.log (812303 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (172368859 / 1000000000) ≤ -Real.log (250000 / 297029) ∧
    -Real.log (250000 / 297029) ≤ (8618443 / 50000000) := by
  have h := checkLog_sound (w := (47029 / 547029)) (n := 12)
    (lo := (172368859 / 1000000000)) (hi := (8618443 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297029 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297029 / 250000) = 1/(250000 / 297029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (172368859 / 1000000000) (8618443 / 50000000) (Real.log (297029 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (297029 / 250000) = -Real.log (250000 / 297029) := by
    rw [show ((297029 / 250000) : ℝ) = ((250000 / 297029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (104198903 / 500000000) ≤ -Real.log (202971 / 250000) ∧
    -Real.log (202971 / 250000) ≤ (208397807 / 1000000000) := by
  have h := checkLog_sound (w := (47029 / 452971)) (n := 12)
    (lo := (104198903 / 500000000)) (hi := (208397807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202971) = 1/(202971 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-208397807 / 1000000000) (-104198903 / 500000000) (Real.log (202971 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125777659 / 1000000000) ≤ -Real.log (100000 / 113403) ∧
    -Real.log (100000 / 113403) ≤ (6288883 / 50000000) := by
  have h := checkLog_sound (w := (13403 / 213403)) (n := 12)
    (lo := (125777659 / 1000000000)) (hi := (6288883 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113403 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113403 / 100000) = 1/(100000 / 113403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125777659 / 1000000000) (6288883 / 50000000) (Real.log (113403 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (113403 / 100000) = -Real.log (100000 / 113403) := by
    rw [show ((113403 / 100000) : ℝ) = ((100000 / 113403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (143905013 / 1000000000) ≤ -Real.log (86597 / 100000) ∧
    -Real.log (86597 / 100000) ≤ (71952507 / 500000000) := by
  have h := checkLog_sound (w := (13403 / 186597)) (n := 12)
    (lo := (143905013 / 1000000000)) (hi := (71952507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 86597) = 1/(86597 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-71952507 / 500000000) (-143905013 / 1000000000) (Real.log (86597 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (126047457 / 1000000000) ≤ -Real.log (15625 / 17724) ∧
    -Real.log (15625 / 17724) ≤ (63023729 / 500000000) := by
  have h := checkLog_sound (w := (2099 / 33349)) (n := 12)
    (lo := (126047457 / 1000000000)) (hi := (63023729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17724 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17724 / 15625) = 1/(15625 / 17724) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (126047457 / 1000000000) (63023729 / 500000000) (Real.log (17724 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (17724 / 15625) = -Real.log (15625 / 17724) := by
    rw [show ((17724 / 15625) : ℝ) = ((15625 / 17724) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (36064609 / 250000000) ≤ -Real.log (13526 / 15625) ∧
    -Real.log (13526 / 15625) ≤ (144258437 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 29151)) (n := 12)
    (lo := (36064609 / 250000000)) (hi := (144258437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13526) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13526) = 1/(13526 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-144258437 / 1000000000) (-36064609 / 250000000) (Real.log (13526 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (271100373 / 500000000) ≤ -Real.log (5000000000 / 8598937583) ∧
    -Real.log (5000000000 / 8598937583) ≤ (542200747 / 1000000000) := by
  have h := checkLog_sound (w := (3598937583 / 13598937583)) (n := 12)
    (lo := (271100373 / 500000000)) (hi := (542200747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8598937583 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8598937583 / 5000000000) = 1/(5000000000 / 8598937583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (271100373 / 500000000) (542200747 / 1000000000) (Real.log (8598937583 / 5000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (8598937583 / 5000000000) = -Real.log (5000000000 / 8598937583) := by
    rw [show ((8598937583 / 5000000000) : ℝ) = ((5000000000 / 8598937583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (543461089 / 1000000000) ≤ -Real.log (125000000000 / 215244550771) ∧
    -Real.log (125000000000 / 215244550771) ≤ (54346109 / 100000000) := by
  have h := checkLog_sound (w := (90244550771 / 340244550771)) (n := 12)
    (lo := (543461089 / 1000000000)) (hi := (54346109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215244550771 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215244550771 / 125000000000) = 1/(125000000000 / 215244550771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (543461089 / 1000000000) (54346109 / 100000000) (Real.log (215244550771 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (215244550771 / 125000000000) = -Real.log (125000000000 / 215244550771) := by
    rw [show ((215244550771 / 125000000000) : ℝ) = ((125000000000 / 215244550771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (379897993 / 1000000000) ≤ -Real.log (500000000000 / 731067717341) ∧
    -Real.log (500000000000 / 731067717341) ≤ (189948997 / 500000000) := by
  have h := checkLog_sound (w := (231067717341 / 1231067717341)) (n := 12)
    (lo := (379897993 / 1000000000)) (hi := (189948997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731067717341 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731067717341 / 500000000000) = 1/(500000000000 / 731067717341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (379897993 / 1000000000) (189948997 / 500000000) (Real.log (731067717341 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (731067717341 / 500000000000) = -Real.log (500000000000 / 731067717341) := by
    rw [show ((731067717341 / 500000000000) : ℝ) = ((500000000000 / 731067717341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76153333 / 200000000) ≤ -Real.log (20000000000 / 29268122047) ∧
    -Real.log (20000000000 / 29268122047) ≤ (190383333 / 500000000) := by
  have h := checkLog_sound (w := (9268122047 / 49268122047)) (n := 12)
    (lo := (76153333 / 200000000)) (hi := (190383333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29268122047 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29268122047 / 20000000000) = 1/(20000000000 / 29268122047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (76153333 / 200000000) (190383333 / 500000000) (Real.log (29268122047 / 20000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (29268122047 / 20000000000) = -Real.log (20000000000 / 29268122047) := by
    rw [show ((29268122047 / 20000000000) : ℝ) = ((20000000000 / 29268122047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (269682673 / 1000000000) ≤ -Real.log (250000000000 / 327387207409) ∧
    -Real.log (250000000000 / 327387207409) ≤ (134841337 / 500000000) := by
  have h := checkLog_sound (w := (77387207409 / 577387207409)) (n := 12)
    (lo := (269682673 / 1000000000)) (hi := (134841337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327387207409 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327387207409 / 250000000000) = 1/(250000000000 / 327387207409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (269682673 / 1000000000) (134841337 / 500000000) (Real.log (327387207409 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (327387207409 / 250000000000) = -Real.log (250000000000 / 327387207409) := by
    rw [show ((327387207409 / 250000000000) : ℝ) = ((250000000000 / 327387207409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (135152947 / 500000000) ≤ -Real.log (125000000000 / 163795652817) ∧
    -Real.log (125000000000 / 163795652817) ≤ (54061179 / 200000000) := by
  have h := checkLog_sound (w := (38795652817 / 288795652817)) (n := 12)
    (lo := (135152947 / 500000000)) (hi := (54061179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163795652817 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163795652817 / 125000000000) = 1/(125000000000 / 163795652817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (135152947 / 500000000) (54061179 / 200000000) (Real.log (163795652817 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (163795652817 / 125000000000) = -Real.log (125000000000 / 163795652817) := by
    rw [show ((163795652817 / 125000000000) : ℝ) = ((125000000000 / 163795652817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9105489 / 500000000) ≤ -Real.log (239734824 / 244140625) ∧
    -Real.log (239734824 / 244140625) ≤ (18210979 / 1000000000) := by
  have h := checkLog_sound (w := (4405801 / 483875449)) (n := 12)
    (lo := (9105489 / 500000000)) (hi := (18210979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 239734824) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 239734824) = 1/(239734824 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18210979 / 1000000000) (-9105489 / 500000000) (Real.log (239734824 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18127353 / 1000000000) ≤ -Real.log (9820359591 / 10000000000) ∧
    -Real.log (9820359591 / 10000000000) ≤ (9063677 / 500000000) := by
  have h := checkLog_sound (w := (179640409 / 19820359591)) (n := 12)
    (lo := (18127353 / 1000000000)) (hi := (9063677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9820359591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9820359591) = 1/(9820359591 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9063677 / 500000000) (-18127353 / 1000000000) (Real.log (9820359591 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell025

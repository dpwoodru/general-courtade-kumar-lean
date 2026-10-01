import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell185
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

theorem reflection_log_1_neg : (306737637 / 1000000000) ≤ -Real.log (2560 / 3479) ∧
    -Real.log (2560 / 3479) ≤ (153368819 / 500000000) := by
  have h := checkLog_sound (w := (919 / 6039)) (n := 12)
    (lo := (306737637 / 1000000000)) (hi := (153368819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3479 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3479 / 2560) = 1/(2560 / 3479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (306737637 / 1000000000) (153368819 / 500000000) (Real.log (3479 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3479 / 2560) = -Real.log (2560 / 3479) := by
    rw [show ((3479 / 2560) : ℝ) = ((2560 / 3479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (222350723 / 500000000) ≤ -Real.log (1641 / 2560) ∧
    -Real.log (1641 / 2560) ≤ (444701447 / 1000000000) := by
  have h := checkLog_sound (w := (919 / 4201)) (n := 12)
    (lo := (222350723 / 500000000)) (hi := (444701447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1641) = 1/(1641 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-444701447 / 1000000000) (-222350723 / 500000000) (Real.log (1641 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (153153193 / 500000000) ≤ -Real.log (1024 / 1391) ∧
    -Real.log (1024 / 1391) ≤ (306306387 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2415)) (n := 12)
    (lo := (153153193 / 500000000)) (hi := (306306387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1391 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1391 / 1024) = 1/(1024 / 1391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (153153193 / 500000000) (306306387 / 1000000000) (Real.log (1391 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1391 / 1024) = -Real.log (1024 / 1391) := by
    rw [show ((1391 / 1024) : ℝ) = ((1024 / 1391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (443787787 / 1000000000) ≤ -Real.log (657 / 1024) ∧
    -Real.log (657 / 1024) ≤ (110946947 / 250000000) := by
  have h := checkLog_sound (w := (367 / 1681)) (n := 12)
    (lo := (443787787 / 1000000000)) (hi := (110946947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 657) = 1/(657 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-110946947 / 250000000) (-443787787 / 1000000000) (Real.log (657 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45404643 / 200000000) ≤ -Real.log (1000000 / 1254859) ∧
    -Real.log (1000000 / 1254859) ≤ (14188951 / 62500000) := by
  have h := checkLog_sound (w := (254859 / 2254859)) (n := 12)
    (lo := (45404643 / 200000000)) (hi := (14188951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254859 / 1000000) = 1/(1000000 / 1254859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45404643 / 200000000) (14188951 / 62500000) (Real.log (1254859 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1254859 / 1000000) = -Real.log (1000000 / 1254859) := by
    rw [show ((1254859 / 1000000) : ℝ) = ((1000000 / 1254859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (36772727 / 125000000) ≤ -Real.log (745141 / 1000000) ∧
    -Real.log (745141 / 1000000) ≤ (294181817 / 1000000000) := by
  have h := checkLog_sound (w := (254859 / 1745141)) (n := 12)
    (lo := (36772727 / 125000000)) (hi := (294181817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745141) = 1/(745141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-294181817 / 1000000000) (-36772727 / 125000000) (Real.log (745141 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (28420031 / 125000000) ≤ -Real.log (500000 / 627641) ∧
    -Real.log (500000 / 627641) ≤ (227360249 / 1000000000) := by
  have h := checkLog_sound (w := (127641 / 1127641)) (n := 12)
    (lo := (28420031 / 125000000)) (hi := (227360249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627641 / 500000) = 1/(500000 / 627641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (28420031 / 125000000) (227360249 / 1000000000) (Real.log (627641 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (627641 / 500000) = -Real.log (500000 / 627641) := by
    rw [show ((627641 / 500000) : ℝ) = ((500000 / 627641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58949931 / 200000000) ≤ -Real.log (372359 / 500000) ∧
    -Real.log (372359 / 500000) ≤ (36843707 / 125000000) := by
  have h := checkLog_sound (w := (127641 / 872359)) (n := 12)
    (lo := (58949931 / 200000000)) (hi := (36843707 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 372359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 372359) = 1/(372359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-36843707 / 125000000) (-58949931 / 200000000) (Real.log (372359 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (21061103 / 125000000) ≤ -Real.log (200000 / 236703) ∧
    -Real.log (200000 / 236703) ≤ (6739553 / 40000000) := by
  have h := checkLog_sound (w := (36703 / 436703)) (n := 12)
    (lo := (21061103 / 125000000)) (hi := (6739553 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236703 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236703 / 200000) = 1/(200000 / 236703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (21061103 / 125000000) (6739553 / 40000000) (Real.log (236703 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (236703 / 200000) = -Real.log (200000 / 236703) := by
    rw [show ((236703 / 200000) : ℝ) = ((200000 / 236703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (202746737 / 1000000000) ≤ -Real.log (163297 / 200000) ∧
    -Real.log (163297 / 200000) ≤ (101373369 / 500000000) := by
  have h := checkLog_sound (w := (36703 / 363297)) (n := 12)
    (lo := (202746737 / 1000000000)) (hi := (101373369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163297) = 1/(163297 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-101373369 / 500000000) (-202746737 / 1000000000) (Real.log (163297 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33750989 / 200000000) ≤ -Real.log (100000 / 118383) ∧
    -Real.log (100000 / 118383) ≤ (84377473 / 500000000) := by
  have h := checkLog_sound (w := (18383 / 218383)) (n := 12)
    (lo := (33750989 / 200000000)) (hi := (84377473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118383 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118383 / 100000) = 1/(100000 / 118383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33750989 / 200000000) (84377473 / 500000000) (Real.log (118383 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (118383 / 100000) = -Real.log (100000 / 118383) := by
    rw [show ((118383 / 100000) : ℝ) = ((100000 / 118383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (50783153 / 250000000) ≤ -Real.log (81617 / 100000) ∧
    -Real.log (81617 / 100000) ≤ (203132613 / 1000000000) := by
  have h := checkLog_sound (w := (18383 / 181617)) (n := 12)
    (lo := (50783153 / 250000000)) (hi := (203132613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81617) = 1/(81617 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-203132613 / 1000000000) (-50783153 / 250000000) (Real.log (81617 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (187523543 / 250000000) ≤ -Real.log (100000000000 / 211719939117) ∧
    -Real.log (100000000000 / 211719939117) ≤ (375047087 / 500000000) := by
  have h := checkLog_sound (w := (11719939117 / 411719939117)) (n := 12)
    (lo := (3559187 / 62500000)) (hi := (56946993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211719939117 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(211719939117 / 200000000000) = 1/(100000000000 / 211719939117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (187523543 / 250000000) (375047087 / 500000000) (Real.log (211719939117 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (211719939117 / 100000000000) = -Real.log (100000000000 / 211719939117) := by
    rw [show ((211719939117 / 100000000000) : ℝ) = ((100000000000 / 211719939117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (751439083 / 1000000000) ≤ -Real.log (500000000000 / 1060024375381) ∧
    -Real.log (500000000000 / 1060024375381) ≤ (150287817 / 200000000) := by
  have h := checkLog_sound (w := (60024375381 / 2060024375381)) (n := 12)
    (lo := (58291903 / 1000000000)) (hi := (910811 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1060024375381 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1060024375381 / 1000000000000) = 1/(500000000000 / 1060024375381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (751439083 / 1000000000) (150287817 / 200000000) (Real.log (1060024375381 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1060024375381 / 500000000000) = -Real.log (500000000000 / 1060024375381) := by
    rw [show ((1060024375381 / 500000000000) : ℝ) = ((500000000000 / 1060024375381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (65150629 / 125000000) ≤ -Real.log (100000000000 / 168405576931) ∧
    -Real.log (100000000000 / 168405576931) ≤ (521205033 / 1000000000) := by
  have h := checkLog_sound (w := (68405576931 / 268405576931)) (n := 12)
    (lo := (65150629 / 125000000)) (hi := (521205033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168405576931 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168405576931 / 100000000000) = 1/(100000000000 / 168405576931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (65150629 / 125000000) (521205033 / 1000000000) (Real.log (168405576931 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (168405576931 / 100000000000) = -Real.log (100000000000 / 168405576931) := by
    rw [show ((168405576931 / 100000000000) : ℝ) = ((100000000000 / 168405576931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (32631869 / 62500000) ≤ -Real.log (125000000000 / 210697539203) ∧
    -Real.log (125000000000 / 210697539203) ≤ (104421981 / 200000000) := by
  have h := checkLog_sound (w := (85697539203 / 335697539203)) (n := 12)
    (lo := (32631869 / 62500000)) (hi := (104421981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210697539203 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210697539203 / 125000000000) = 1/(125000000000 / 210697539203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (32631869 / 62500000) (104421981 / 200000000) (Real.log (210697539203 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (210697539203 / 125000000000) = -Real.log (125000000000 / 210697539203) := by
    rw [show ((210697539203 / 125000000000) : ℝ) = ((125000000000 / 210697539203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (371235561 / 1000000000) ≤ -Real.log (500000000000 / 724762243029) ∧
    -Real.log (500000000000 / 724762243029) ≤ (185617781 / 500000000) := by
  have h := checkLog_sound (w := (224762243029 / 1224762243029)) (n := 12)
    (lo := (371235561 / 1000000000)) (hi := (185617781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724762243029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724762243029 / 500000000000) = 1/(500000000000 / 724762243029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (371235561 / 1000000000) (185617781 / 500000000) (Real.log (724762243029 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (724762243029 / 500000000000) = -Real.log (500000000000 / 724762243029) := by
    rw [show ((724762243029 / 500000000000) : ℝ) = ((500000000000 / 724762243029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (371887557 / 1000000000) ≤ -Real.log (1250000000 / 1813087347) ∧
    -Real.log (1250000000 / 1813087347) ≤ (185943779 / 500000000) := by
  have h := checkLog_sound (w := (563087347 / 3063087347)) (n := 12)
    (lo := (371887557 / 1000000000)) (hi := (185943779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1813087347 / 1250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1813087347 / 1250000000) = 1/(1250000000 / 1813087347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (371887557 / 1000000000) (185943779 / 500000000) (Real.log (1813087347 / 1250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1813087347 / 1250000000) = -Real.log (1250000000 / 1813087347) := by
    rw [show ((1813087347 / 1250000000) : ℝ) = ((1250000000 / 1813087347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34377667 / 1000000000) ≤ -Real.log (9662065311 / 10000000000) ∧
    -Real.log (9662065311 / 10000000000) ≤ (8594417 / 250000000) := by
  have h := checkLog_sound (w := (337934689 / 19662065311)) (n := 12)
    (lo := (34377667 / 1000000000)) (hi := (8594417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9662065311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9662065311) = 1/(9662065311 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8594417 / 250000000) (-34377667 / 1000000000) (Real.log (9662065311 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (34257913 / 1000000000) ≤ -Real.log (38652889791 / 40000000000) ∧
    -Real.log (38652889791 / 40000000000) ≤ (17128957 / 500000000) := by
  have h := checkLog_sound (w := (1347110209 / 78652889791)) (n := 12)
    (lo := (34257913 / 1000000000)) (hi := (17128957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38652889791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38652889791) = 1/(38652889791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-17128957 / 500000000) (-34257913 / 1000000000) (Real.log (38652889791 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell185

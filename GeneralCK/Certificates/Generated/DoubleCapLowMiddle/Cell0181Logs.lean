import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0181
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

theorem reflection_log_1_neg : (78054161 / 125000000) ≤ -Real.log (128 / 239) ∧
    -Real.log (128 / 239) ≤ (624433289 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 367)) (n := 12)
    (lo := (78054161 / 125000000)) (hi := (624433289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239 / 128) = 1/(128 / 239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (78054161 / 125000000) (624433289 / 1000000000) (Real.log (239 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (239 / 128) = -Real.log (128 / 239) := by
    rw [show ((239 / 128) : ℝ) = ((128 / 239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1009408459 / 500000000) ≤ -Real.log (17 / 128) ∧
    -Real.log (17 / 128) ≤ (2018816921 / 1000000000) := by
  have h := checkLog_sound (w := (15 / 49)) (n := 12)
    (lo := (316261279 / 500000000)) (hi := (632522559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 17) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 17) = 1/(17 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2018816921 / 1000000000) (-1009408459 / 500000000) (Real.log (17 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (38927629 / 62500000) ≤ -Real.log (6400 / 11931) ∧
    -Real.log (6400 / 11931) ≤ (124568413 / 200000000) := by
  have h := checkLog_sound (w := (5531 / 18331)) (n := 12)
    (lo := (38927629 / 62500000)) (hi := (124568413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11931 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11931 / 6400) = 1/(6400 / 11931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (38927629 / 62500000) (124568413 / 200000000) (Real.log (11931 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11931 / 6400) = -Real.log (6400 / 11931) := by
    rw [show ((11931 / 6400) : ℝ) = ((6400 / 11931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (998355071 / 500000000) ≤ -Real.log (869 / 6400) ∧
    -Real.log (869 / 6400) ≤ (399342029 / 200000000) := by
  have h := checkLog_sound (w := (731 / 2469)) (n := 12)
    (lo := (305207891 / 500000000)) (hi := (610415783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 869) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 869) = 1/(869 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-399342029 / 200000000) (-998355071 / 500000000) (Real.log (869 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (550647117 / 1000000000) ≤ -Real.log (64 / 111) ∧
    -Real.log (64 / 111) ≤ (275323559 / 500000000) := by
  have h := checkLog_sound (w := (47 / 175)) (n := 12)
    (lo := (550647117 / 1000000000)) (hi := (275323559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111 / 64) = 1/(64 / 111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (550647117 / 1000000000) (275323559 / 500000000) (Real.log (111 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (111 / 64) = -Real.log (64 / 111) := by
    rw [show ((111 / 64) : ℝ) = ((64 / 111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (662834869 / 500000000) ≤ -Real.log (17 / 64) ∧
    -Real.log (17 / 64) ≤ (66283487 / 50000000) := by
  have h := checkLog_sound (w := (15 / 49)) (n := 12)
    (lo := (316261279 / 500000000)) (hi := (632522559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 17) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 17) = 1/(17 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-66283487 / 50000000) (-662834869 / 500000000) (Real.log (17 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (547217821 / 1000000000) ≤ -Real.log (3200 / 5531) ∧
    -Real.log (3200 / 5531) ≤ (273608911 / 500000000) := by
  have h := checkLog_sound (w := (2331 / 8731)) (n := 12)
    (lo := (547217821 / 1000000000)) (hi := (273608911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5531 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5531 / 3200) = 1/(3200 / 5531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (547217821 / 1000000000) (273608911 / 500000000) (Real.log (5531 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5531 / 3200) = -Real.log (3200 / 5531) := by
    rw [show ((5531 / 3200) : ℝ) = ((3200 / 5531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (651781481 / 500000000) ≤ -Real.log (869 / 3200) ∧
    -Real.log (869 / 3200) ≤ (325890741 / 250000000) := by
  have h := checkLog_sound (w := (731 / 2469)) (n := 12)
    (lo := (305207891 / 500000000)) (hi := (610415783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 869) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 869) = 1/(869 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-325890741 / 250000000) (-651781481 / 500000000) (Real.log (869 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (641817569 / 1000000000) ≤ -Real.log (1000000 / 1899931) ∧
    -Real.log (1000000 / 1899931) ≤ (64181757 / 100000000) := by
  have h := checkLog_sound (w := (899931 / 2899931)) (n := 12)
    (lo := (641817569 / 1000000000)) (hi := (64181757 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899931 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899931 / 1000000) = 1/(1000000 / 1899931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (641817569 / 1000000000) (64181757 / 100000000) (Real.log (1899931 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1899931 / 1000000) = -Real.log (1000000 / 1899931) := by
    rw [show ((1899931 / 1000000) : ℝ) = ((1000000 / 1899931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2301895329 / 1000000000) ≤ -Real.log (100069 / 1000000) ∧
    -Real.log (100069 / 1000000) ≤ (2301895333 / 1000000000) := by
  have h := checkLog_sound (w := (24931 / 225069)) (n := 12)
    (lo := (222453789 / 1000000000)) (hi := (22245379 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100069) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 100069) = 1/(100069 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2301895333 / 1000000000) (-2301895329 / 1000000000) (Real.log (100069 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (642803961 / 1000000000) ≤ -Real.log (500000 / 950903) ∧
    -Real.log (500000 / 950903) ≤ (321401981 / 500000000) := by
  have h := checkLog_sound (w := (450903 / 1450903)) (n := 12)
    (lo := (642803961 / 1000000000)) (hi := (321401981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((950903 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(950903 / 500000) = 1/(500000 / 950903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (642803961 / 1000000000) (321401981 / 500000000) (Real.log (950903 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (950903 / 500000) = -Real.log (500000 / 950903) := by
    rw [show ((950903 / 500000) : ℝ) = ((500000 / 950903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2320810163 / 1000000000) ≤ -Real.log (49097 / 500000) ∧
    -Real.log (49097 / 500000) ≤ (2320810167 / 1000000000) := by
  have h := checkLog_sound (w := (13403 / 111597)) (n := 12)
    (lo := (241368623 / 1000000000)) (hi := (15085539 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49097) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 49097) = 1/(49097 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2320810167 / 1000000000) (-2320810163 / 1000000000) (Real.log (49097 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2497097 / 3906250) ≤ -Real.log (31250 / 59221) ∧
    -Real.log (31250 / 59221) ≤ (639256833 / 1000000000) := by
  have h := checkLog_sound (w := (27971 / 90471)) (n := 12)
    (lo := (2497097 / 3906250)) (hi := (639256833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59221 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59221 / 31250) = 1/(31250 / 59221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2497097 / 3906250) (639256833 / 1000000000) (Real.log (59221 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (59221 / 31250) = -Real.log (31250 / 59221) := by
    rw [show ((59221 / 31250) : ℝ) = ((31250 / 59221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (563620219 / 250000000) ≤ -Real.log (3279 / 31250) ∧
    -Real.log (3279 / 31250) ≤ (28181011 / 12500000) := by
  have h := checkLog_sound (w := (2509 / 28741)) (n := 12)
    (lo := (21879917 / 125000000)) (hi := (175039337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13116) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 13116) = 1/(3279 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-28181011 / 12500000) (-563620219 / 250000000) (Real.log (3279 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (40023497 / 62500000) ≤ -Real.log (500000 / 948597) ∧
    -Real.log (500000 / 948597) ≤ (640375953 / 1000000000) := by
  have h := checkLog_sound (w := (448597 / 1448597)) (n := 12)
    (lo := (40023497 / 62500000)) (hi := (640375953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((948597 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(948597 / 500000) = 1/(500000 / 948597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (40023497 / 62500000) (640375953 / 1000000000) (Real.log (948597 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (948597 / 500000) = -Real.log (500000 / 948597) := by
    rw [show ((948597 / 500000) : ℝ) = ((500000 / 948597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (56872789 / 25000000) ≤ -Real.log (51403 / 500000) ∧
    -Real.log (51403 / 500000) ≤ (568727891 / 250000000) := by
  have h := checkLog_sound (w := (11097 / 113903)) (n := 12)
    (lo := (9773501 / 50000000)) (hi := (195470021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51403) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 51403) = 1/(51403 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-568727891 / 250000000) (-56872789 / 25000000) (Real.log (51403 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1471856449 / 500000000) ≤ -Real.log (500000000000 / 9493104757717) ∧
    -Real.log (500000000000 / 9493104757717) ≤ (2943712903 / 1000000000) := by
  have h := checkLog_sound (w := (1493104757717 / 17493104757717)) (n := 12)
    (lo := (85562089 / 500000000)) (hi := (171124179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9493104757717 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9493104757717 / 8000000000000) = 1/(500000000000 / 9493104757717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1471856449 / 500000000) (2943712903 / 1000000000) (Real.log (9493104757717 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9493104757717 / 500000000000) = -Real.log (500000000000 / 9493104757717) := by
    rw [show ((9493104757717 / 500000000000) : ℝ) = ((500000000000 / 9493104757717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (740903531 / 250000000) ≤ -Real.log (25000000000 / 484196081227) ∧
    -Real.log (25000000000 / 484196081227) ≤ (2963614129 / 1000000000) := by
  have h := checkLog_sound (w := (84196081227 / 884196081227)) (n := 12)
    (lo := (47756351 / 250000000)) (hi := (38205081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484196081227 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(484196081227 / 400000000000) = 1/(25000000000 / 484196081227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (740903531 / 250000000) (2963614129 / 1000000000) (Real.log (484196081227 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (484196081227 / 25000000000) = -Real.log (25000000000 / 484196081227) := by
    rw [show ((484196081227 / 25000000000) : ℝ) = ((25000000000 / 484196081227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (723434427 / 250000000) ≤ -Real.log (500000000000 / 9030344617261) ∧
    -Real.log (500000000000 / 9030344617261) ≤ (2893737713 / 1000000000) := by
  have h := checkLog_sound (w := (1030344617261 / 17030344617261)) (n := 12)
    (lo := (30287247 / 250000000)) (hi := (121148989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9030344617261 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9030344617261 / 8000000000000) = 1/(500000000000 / 9030344617261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (723434427 / 250000000) (2893737713 / 1000000000) (Real.log (9030344617261 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9030344617261 / 500000000000) = -Real.log (500000000000 / 9030344617261) := by
    rw [show ((9030344617261 / 500000000000) : ℝ) = ((500000000000 / 9030344617261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (364410939 / 125000000) ≤ -Real.log (500000000000 / 9227058731981) ∧
    -Real.log (500000000000 / 9227058731981) ≤ (2915287517 / 1000000000) := by
  have h := checkLog_sound (w := (1227058731981 / 17227058731981)) (n := 12)
    (lo := (17837349 / 125000000)) (hi := (142698793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9227058731981 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9227058731981 / 8000000000000) = 1/(500000000000 / 9227058731981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (364410939 / 125000000) (2915287517 / 1000000000) (Real.log (9227058731981 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9227058731981 / 500000000000) = -Real.log (500000000000 / 9227058731981) := by
    rw [show ((9227058731981 / 500000000000) : ℝ) = ((500000000000 / 9227058731981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0181

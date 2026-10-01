import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell044
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

theorem reflection_log_1_neg : (61004477 / 250000000) ≤ -Real.log (1024 / 1307) ∧
    -Real.log (1024 / 1307) ≤ (244017909 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 2331)) (n := 12)
    (lo := (61004477 / 250000000)) (hi := (244017909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307 / 1024) = 1/(1024 / 1307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (61004477 / 250000000) (244017909 / 1000000000) (Real.log (1307 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1307 / 1024) = -Real.log (1024 / 1307) := by
    rw [show ((1307 / 1024) : ℝ) = ((1024 / 1307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16173559 / 50000000) ≤ -Real.log (741 / 1024) ∧
    -Real.log (741 / 1024) ≤ (323471181 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 1765)) (n := 12)
    (lo := (16173559 / 50000000)) (hi := (323471181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 741) = 1/(741 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-323471181 / 1000000000) (-16173559 / 50000000) (Real.log (741 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (15222421 / 62500000) ≤ -Real.log (1280 / 1633) ∧
    -Real.log (1280 / 1633) ≤ (243558737 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 2913)) (n := 12)
    (lo := (15222421 / 62500000)) (hi := (243558737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1633 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1633 / 1280) = 1/(1280 / 1633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (15222421 / 62500000) (243558737 / 1000000000) (Real.log (1633 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1633 / 1280) = -Real.log (1280 / 1633) := by
    rw [show ((1633 / 1280) : ℝ) = ((1280 / 1633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (322661791 / 1000000000) ≤ -Real.log (927 / 1280) ∧
    -Real.log (927 / 1280) ≤ (10083181 / 31250000) := by
  have h := checkLog_sound (w := (353 / 2207)) (n := 12)
    (lo := (322661791 / 1000000000)) (hi := (10083181 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 927) = 1/(927 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10083181 / 31250000) (-322661791 / 1000000000) (Real.log (927 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (22335619 / 125000000) ≤ -Real.log (250000 / 298911) ∧
    -Real.log (250000 / 298911) ≤ (178684953 / 1000000000) := by
  have h := checkLog_sound (w := (48911 / 548911)) (n := 12)
    (lo := (22335619 / 125000000)) (hi := (178684953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298911 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298911 / 250000) = 1/(250000 / 298911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (22335619 / 125000000) (178684953 / 1000000000) (Real.log (298911 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (298911 / 250000) = -Real.log (250000 / 298911) := by
    rw [show ((298911 / 250000) : ℝ) = ((250000 / 298911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (217713321 / 1000000000) ≤ -Real.log (201089 / 250000) ∧
    -Real.log (201089 / 250000) ≤ (108856661 / 500000000) := by
  have h := checkLog_sound (w := (48911 / 451089)) (n := 12)
    (lo := (217713321 / 1000000000)) (hi := (108856661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201089) = 1/(201089 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-108856661 / 500000000) (-217713321 / 1000000000) (Real.log (201089 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (35807233 / 200000000) ≤ -Real.log (31250 / 37377) ∧
    -Real.log (31250 / 37377) ≤ (89518083 / 500000000) := by
  have h := checkLog_sound (w := (6127 / 68627)) (n := 12)
    (lo := (35807233 / 200000000)) (hi := (89518083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37377 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37377 / 31250) = 1/(31250 / 37377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (35807233 / 200000000) (89518083 / 500000000) (Real.log (37377 / 31250)) := by
  have h := reflection_log_7_neg
  have he : Real.log (37377 / 31250) = -Real.log (31250 / 37377) := by
    rw [show ((37377 / 31250) : ℝ) = ((31250 / 37377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (109117807 / 500000000) ≤ -Real.log (25123 / 31250) ∧
    -Real.log (25123 / 31250) ≤ (43647123 / 200000000) := by
  have h := checkLog_sound (w := (6127 / 56373)) (n := 12)
    (lo := (109117807 / 500000000)) (hi := (43647123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25123) = 1/(25123 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-43647123 / 200000000) (-109117807 / 500000000) (Real.log (25123 / 31250)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (130874741 / 1000000000) ≤ -Real.log (40000 / 45593) ∧
    -Real.log (40000 / 45593) ≤ (65437371 / 500000000) := by
  have h := checkLog_sound (w := (5593 / 85593)) (n := 12)
    (lo := (130874741 / 1000000000)) (hi := (65437371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45593 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45593 / 40000) = 1/(40000 / 45593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (130874741 / 1000000000) (65437371 / 500000000) (Real.log (45593 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (45593 / 40000) = -Real.log (40000 / 45593) := by
    rw [show ((45593 / 40000) : ℝ) = ((40000 / 45593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (75309711 / 500000000) ≤ -Real.log (34407 / 40000) ∧
    -Real.log (34407 / 40000) ≤ (150619423 / 1000000000) := by
  have h := checkLog_sound (w := (5593 / 74407)) (n := 12)
    (lo := (75309711 / 500000000)) (hi := (150619423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 34407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 34407) = 1/(34407 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-150619423 / 1000000000) (-75309711 / 500000000) (Real.log (34407 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (256139 / 1953125) ≤ -Real.log (1000000 / 1140131) ∧
    -Real.log (1000000 / 1140131) ≤ (131143169 / 1000000000) := by
  have h := checkLog_sound (w := (140131 / 2140131)) (n := 12)
    (lo := (256139 / 1953125)) (hi := (131143169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1140131 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1140131 / 1000000) = 1/(1000000 / 1140131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (256139 / 1953125) (131143169 / 1000000000) (Real.log (1140131 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1140131 / 1000000) = -Real.log (1000000 / 1140131) := by
    rw [show ((1140131 / 1000000) : ℝ) = ((1000000 / 1140131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (75487613 / 500000000) ≤ -Real.log (859869 / 1000000) ∧
    -Real.log (859869 / 1000000) ≤ (150975227 / 1000000000) := by
  have h := checkLog_sound (w := (140131 / 1859869)) (n := 12)
    (lo := (75487613 / 500000000)) (hi := (150975227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 859869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 859869) = 1/(859869 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-150975227 / 1000000000) (-75487613 / 500000000) (Real.log (859869 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (566220527 / 1000000000) ≤ -Real.log (250000000000 / 440399137001) ∧
    -Real.log (250000000000 / 440399137001) ≤ (35388783 / 62500000) := by
  have h := checkLog_sound (w := (190399137001 / 690399137001)) (n := 12)
    (lo := (566220527 / 1000000000)) (hi := (35388783 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((440399137001 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(440399137001 / 250000000000) = 1/(250000000000 / 440399137001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (566220527 / 1000000000) (35388783 / 62500000) (Real.log (440399137001 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (440399137001 / 250000000000) = -Real.log (250000000000 / 440399137001) := by
    rw [show ((440399137001 / 250000000000) : ℝ) = ((250000000000 / 440399137001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (8867017 / 15625000) ≤ -Real.log (100000000000 / 176383265857) ∧
    -Real.log (100000000000 / 176383265857) ≤ (567489089 / 1000000000) := by
  have h := checkLog_sound (w := (76383265857 / 276383265857)) (n := 12)
    (lo := (8867017 / 15625000)) (hi := (567489089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176383265857 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176383265857 / 100000000000) = 1/(100000000000 / 176383265857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (8867017 / 15625000) (567489089 / 1000000000) (Real.log (176383265857 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (176383265857 / 100000000000) = -Real.log (100000000000 / 176383265857) := by
    rw [show ((176383265857 / 100000000000) : ℝ) = ((100000000000 / 176383265857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (198199137 / 500000000) ≤ -Real.log (125000000000 / 185807652333) ∧
    -Real.log (125000000000 / 185807652333) ≤ (15855931 / 40000000) := by
  have h := checkLog_sound (w := (60807652333 / 310807652333)) (n := 12)
    (lo := (198199137 / 500000000)) (hi := (15855931 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185807652333 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185807652333 / 125000000000) = 1/(125000000000 / 185807652333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (198199137 / 500000000) (15855931 / 40000000) (Real.log (185807652333 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (185807652333 / 125000000000) = -Real.log (125000000000 / 185807652333) := by
    rw [show ((185807652333 / 125000000000) : ℝ) = ((125000000000 / 185807652333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (19863589 / 50000000) ≤ -Real.log (25000000000 / 37194005493) ∧
    -Real.log (25000000000 / 37194005493) ≤ (397271781 / 1000000000) := by
  have h := checkLog_sound (w := (12194005493 / 62194005493)) (n := 12)
    (lo := (19863589 / 50000000)) (hi := (397271781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37194005493 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37194005493 / 25000000000) = 1/(25000000000 / 37194005493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (19863589 / 50000000) (397271781 / 1000000000) (Real.log (37194005493 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (37194005493 / 25000000000) = -Real.log (25000000000 / 37194005493) := by
    rw [show ((37194005493 / 25000000000) : ℝ) = ((25000000000 / 37194005493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (281494163 / 1000000000) ≤ -Real.log (250000000000 / 331277065713) ∧
    -Real.log (250000000000 / 331277065713) ≤ (70373541 / 250000000) := by
  have h := checkLog_sound (w := (81277065713 / 581277065713)) (n := 12)
    (lo := (281494163 / 1000000000)) (hi := (70373541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331277065713 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331277065713 / 250000000000) = 1/(250000000000 / 331277065713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (281494163 / 1000000000) (70373541 / 250000000) (Real.log (331277065713 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (331277065713 / 250000000000) = -Real.log (250000000000 / 331277065713) := by
    rw [show ((331277065713 / 250000000000) : ℝ) = ((250000000000 / 331277065713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (56423679 / 200000000) ≤ -Real.log (125000000000 / 165741961857) ∧
    -Real.log (125000000000 / 165741961857) ≤ (70529599 / 250000000) := by
  have h := checkLog_sound (w := (40741961857 / 290741961857)) (n := 12)
    (lo := (56423679 / 200000000)) (hi := (70529599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165741961857 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165741961857 / 125000000000) = 1/(125000000000 / 165741961857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (56423679 / 200000000) (70529599 / 250000000) (Real.log (165741961857 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (165741961857 / 125000000000) = -Real.log (125000000000 / 165741961857) := by
    rw [show ((165741961857 / 125000000000) : ℝ) = ((125000000000 / 165741961857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9916029 / 500000000) ≤ -Real.log (980363302839 / 1000000000000) ∧
    -Real.log (980363302839 / 1000000000000) ≤ (19832059 / 1000000000) := by
  have h := checkLog_sound (w := (19636697161 / 1980363302839)) (n := 12)
    (lo := (9916029 / 500000000)) (hi := (19832059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980363302839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980363302839) = 1/(980363302839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19832059 / 1000000000) (-9916029 / 500000000) (Real.log (980363302839 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (493617 / 25000000) ≤ -Real.log (1568718351 / 1600000000) ∧
    -Real.log (1568718351 / 1600000000) ≤ (19744681 / 1000000000) := by
  have h := checkLog_sound (w := (31281649 / 3168718351)) (n := 12)
    (lo := (493617 / 25000000)) (hi := (19744681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1568718351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1568718351) = 1/(1568718351 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19744681 / 1000000000) (-493617 / 25000000) (Real.log (1568718351 / 1600000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell044

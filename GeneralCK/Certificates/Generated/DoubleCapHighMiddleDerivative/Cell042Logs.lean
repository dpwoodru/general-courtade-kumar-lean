import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell042
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

theorem reflection_log_1_neg : (243099353 / 1000000000) ≤ -Real.log (5120 / 6529) ∧
    -Real.log (5120 / 6529) ≤ (121549677 / 500000000) := by
  have h := checkLog_sound (w := (1409 / 11649)) (n := 12)
    (lo := (243099353 / 1000000000)) (hi := (121549677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6529 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6529 / 5120) = 1/(5120 / 6529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (243099353 / 1000000000) (121549677 / 500000000) (Real.log (6529 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6529 / 5120) = -Real.log (5120 / 6529) := by
    rw [show ((6529 / 5120) : ℝ) = ((5120 / 6529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2514477 / 7812500) ≤ -Real.log (3711 / 5120) ∧
    -Real.log (3711 / 5120) ≤ (321853057 / 1000000000) := by
  have h := checkLog_sound (w := (1409 / 8831)) (n := 12)
    (lo := (2514477 / 7812500)) (hi := (321853057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3711) = 1/(3711 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-321853057 / 1000000000) (-2514477 / 7812500) (Real.log (3711 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (242639759 / 1000000000) ≤ -Real.log (2560 / 3263) ∧
    -Real.log (2560 / 3263) ≤ (3032997 / 12500000) := by
  have h := checkLog_sound (w := (703 / 5823)) (n := 12)
    (lo := (242639759 / 1000000000)) (hi := (3032997 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3263 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3263 / 2560) = 1/(2560 / 3263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (242639759 / 1000000000) (3032997 / 12500000) (Real.log (3263 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3263 / 2560) = -Real.log (2560 / 3263) := by
    rw [show ((3263 / 2560) : ℝ) = ((2560 / 3263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (20065311 / 62500000) ≤ -Real.log (1857 / 2560) ∧
    -Real.log (1857 / 2560) ≤ (321044977 / 1000000000) := by
  have h := checkLog_sound (w := (703 / 4417)) (n := 12)
    (lo := (20065311 / 62500000)) (hi := (321044977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1857) = 1/(1857 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-321044977 / 1000000000) (-20065311 / 62500000) (Real.log (1857 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (177985503 / 1000000000) ≤ -Real.log (125000 / 149351) ∧
    -Real.log (125000 / 149351) ≤ (5562047 / 31250000) := by
  have h := checkLog_sound (w := (24351 / 274351)) (n := 12)
    (lo := (177985503 / 1000000000)) (hi := (5562047 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149351 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149351 / 125000) = 1/(125000 / 149351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (177985503 / 1000000000) (5562047 / 31250000) (Real.log (149351 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (149351 / 125000) = -Real.log (125000 / 149351) := by
    rw [show ((149351 / 125000) : ℝ) = ((125000 / 149351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (5416863 / 25000000) ≤ -Real.log (100649 / 125000) ∧
    -Real.log (100649 / 125000) ≤ (216674521 / 1000000000) := by
  have h := checkLog_sound (w := (24351 / 225649)) (n := 12)
    (lo := (5416863 / 25000000)) (hi := (216674521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 100649) = 1/(100649 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-216674521 / 1000000000) (-5416863 / 25000000) (Real.log (100649 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1426689 / 8000000) ≤ -Real.log (1000000 / 1195227) ∧
    -Real.log (1000000 / 1195227) ≤ (89168063 / 500000000) := by
  have h := checkLog_sound (w := (195227 / 2195227)) (n := 12)
    (lo := (1426689 / 8000000)) (hi := (89168063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1195227 / 1000000) = 1/(1000000 / 1195227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1426689 / 8000000) (89168063 / 500000000) (Real.log (1195227 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1195227 / 1000000) = -Real.log (1000000 / 1195227) := by
    rw [show ((1195227 / 1000000) : ℝ) = ((1000000 / 1195227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (54298757 / 250000000) ≤ -Real.log (804773 / 1000000) ∧
    -Real.log (804773 / 1000000) ≤ (217195029 / 1000000000) := by
  have h := checkLog_sound (w := (195227 / 1804773)) (n := 12)
    (lo := (54298757 / 250000000)) (hi := (217195029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 804773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 804773) = 1/(804773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-217195029 / 1000000000) (-54298757 / 250000000) (Real.log (804773 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2606771 / 20000000) ≤ -Real.log (500000 / 569607) ∧
    -Real.log (500000 / 569607) ≤ (130338551 / 1000000000) := by
  have h := checkLog_sound (w := (69607 / 1069607)) (n := 12)
    (lo := (2606771 / 20000000)) (hi := (130338551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569607 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569607 / 500000) = 1/(500000 / 569607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2606771 / 20000000) (130338551 / 1000000000) (Real.log (569607 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (569607 / 500000) = -Real.log (500000 / 569607) := by
    rw [show ((569607 / 500000) : ℝ) = ((500000 / 569607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (149909353 / 1000000000) ≤ -Real.log (430393 / 500000) ∧
    -Real.log (430393 / 500000) ≤ (74954677 / 500000000) := by
  have h := checkLog_sound (w := (69607 / 930393)) (n := 12)
    (lo := (149909353 / 1000000000)) (hi := (74954677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 430393) = 1/(430393 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-74954677 / 500000000) (-149909353 / 1000000000) (Real.log (430393 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (130607121 / 1000000000) ≤ -Real.log (3125 / 3561) ∧
    -Real.log (3125 / 3561) ≤ (65303561 / 500000000) := by
  have h := checkLog_sound (w := (218 / 3343)) (n := 12)
    (lo := (130607121 / 1000000000)) (hi := (65303561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3561 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3561 / 3125) = 1/(3125 / 3561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (130607121 / 1000000000) (65303561 / 500000000) (Real.log (3561 / 3125)) := by
  have h := reflection_log_11_neg
  have he : Real.log (3561 / 3125) = -Real.log (3125 / 3561) := by
    rw [show ((3561 / 3125) : ℝ) = ((3125 / 3561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (30052981 / 200000000) ≤ -Real.log (2689 / 3125) ∧
    -Real.log (2689 / 3125) ≤ (75132453 / 500000000) := by
  have h := checkLog_sound (w := (218 / 2907)) (n := 12)
    (lo := (30052981 / 200000000)) (hi := (75132453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2689) = 1/(2689 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-75132453 / 500000000) (-30052981 / 200000000) (Real.log (2689 / 3125)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (112736947 / 200000000) ≤ -Real.log (500000000000 / 878567582121) ∧
    -Real.log (500000000000 / 878567582121) ≤ (4403787 / 7812500) := by
  have h := checkLog_sound (w := (378567582121 / 1378567582121)) (n := 12)
    (lo := (112736947 / 200000000)) (hi := (4403787 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((878567582121 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(878567582121 / 500000000000) = 1/(500000000000 / 878567582121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (112736947 / 200000000) (4403787 / 7812500) (Real.log (878567582121 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (878567582121 / 500000000000) = -Real.log (500000000000 / 878567582121) := by
    rw [show ((878567582121 / 500000000000) : ℝ) = ((500000000000 / 878567582121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (56495241 / 100000000) ≤ -Real.log (62500000000 / 109960253301) ∧
    -Real.log (62500000000 / 109960253301) ≤ (564952411 / 1000000000) := by
  have h := checkLog_sound (w := (47460253301 / 172460253301)) (n := 12)
    (lo := (56495241 / 100000000)) (hi := (564952411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109960253301 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109960253301 / 62500000000) = 1/(62500000000 / 109960253301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (56495241 / 100000000) (564952411 / 1000000000) (Real.log (109960253301 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (109960253301 / 62500000000) = -Real.log (62500000000 / 109960253301) := by
    rw [show ((109960253301 / 62500000000) : ℝ) = ((62500000000 / 109960253301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (394660023 / 1000000000) ≤ -Real.log (500000000000 / 741939810629) ∧
    -Real.log (500000000000 / 741939810629) ≤ (49332503 / 125000000) := by
  have h := checkLog_sound (w := (241939810629 / 1241939810629)) (n := 12)
    (lo := (394660023 / 1000000000)) (hi := (49332503 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741939810629 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741939810629 / 500000000000) = 1/(500000000000 / 741939810629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (394660023 / 1000000000) (49332503 / 125000000) (Real.log (741939810629 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (741939810629 / 500000000000) = -Real.log (500000000000 / 741939810629) := by
    rw [show ((741939810629 / 500000000000) : ℝ) = ((500000000000 / 741939810629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (197765577 / 500000000) ≤ -Real.log (500000000000 / 742586418779) ∧
    -Real.log (500000000000 / 742586418779) ≤ (79106231 / 200000000) := by
  have h := checkLog_sound (w := (242586418779 / 1242586418779)) (n := 12)
    (lo := (197765577 / 500000000)) (hi := (79106231 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742586418779 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742586418779 / 500000000000) = 1/(500000000000 / 742586418779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (197765577 / 500000000) (79106231 / 200000000) (Real.log (742586418779 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (742586418779 / 500000000000) = -Real.log (500000000000 / 742586418779) := by
    rw [show ((742586418779 / 500000000000) : ℝ) = ((500000000000 / 742586418779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (8757747 / 31250000) ≤ -Real.log (62500000000 / 82716116433) ∧
    -Real.log (62500000000 / 82716116433) ≤ (56049581 / 200000000) := by
  have h := checkLog_sound (w := (20216116433 / 145216116433)) (n := 12)
    (lo := (8757747 / 31250000)) (hi := (56049581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82716116433 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82716116433 / 62500000000) = 1/(62500000000 / 82716116433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (8757747 / 31250000) (56049581 / 200000000) (Real.log (82716116433 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (82716116433 / 62500000000) = -Real.log (62500000000 / 82716116433) := by
    rw [show ((82716116433 / 62500000000) : ℝ) = ((62500000000 / 82716116433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (280872027 / 1000000000) ≤ -Real.log (250000000000 / 331071030123) ∧
    -Real.log (250000000000 / 331071030123) ≤ (70218007 / 250000000) := by
  have h := checkLog_sound (w := (81071030123 / 581071030123)) (n := 12)
    (lo := (280872027 / 1000000000)) (hi := (70218007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331071030123 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331071030123 / 250000000000) = 1/(250000000000 / 331071030123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (280872027 / 1000000000) (70218007 / 250000000) (Real.log (331071030123 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (331071030123 / 250000000000) = -Real.log (250000000000 / 331071030123) := by
    rw [show ((331071030123 / 250000000000) : ℝ) = ((250000000000 / 331071030123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2457223 / 125000000) ≤ -Real.log (9575529 / 9765625) ∧
    -Real.log (9575529 / 9765625) ≤ (3931557 / 200000000) := by
  have h := checkLog_sound (w := (95048 / 9670577)) (n := 12)
    (lo := (2457223 / 125000000)) (hi := (3931557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9575529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9575529) = 1/(9575529 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3931557 / 200000000) (-2457223 / 125000000) (Real.log (9575529 / 9765625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (9785401 / 500000000) ≤ -Real.log (245154865551 / 250000000000) ∧
    -Real.log (245154865551 / 250000000000) ≤ (19570803 / 1000000000) := by
  have h := checkLog_sound (w := (4845134449 / 495154865551)) (n := 12)
    (lo := (9785401 / 500000000)) (hi := (19570803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245154865551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245154865551) = 1/(245154865551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19570803 / 1000000000) (-9785401 / 500000000) (Real.log (245154865551 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell042

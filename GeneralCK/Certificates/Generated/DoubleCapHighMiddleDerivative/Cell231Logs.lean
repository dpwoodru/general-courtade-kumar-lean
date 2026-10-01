import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell231
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

theorem reflection_log_1_neg : (65275361 / 200000000) ≤ -Real.log (640 / 887) ∧
    -Real.log (640 / 887) ≤ (163188403 / 500000000) := by
  have h := checkLog_sound (w := (247 / 1527)) (n := 12)
    (lo := (65275361 / 200000000)) (hi := (163188403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887 / 640) = 1/(640 / 887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65275361 / 200000000) (163188403 / 500000000) (Real.log (887 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (887 / 640) = -Real.log (640 / 887) := by
    rw [show ((887 / 640) : ℝ) = ((640 / 887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (121914641 / 250000000) ≤ -Real.log (393 / 640) ∧
    -Real.log (393 / 640) ≤ (97531713 / 200000000) := by
  have h := checkLog_sound (w := (247 / 1033)) (n := 12)
    (lo := (121914641 / 250000000)) (hi := (97531713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 393) = 1/(393 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-97531713 / 200000000) (-121914641 / 250000000) (Real.log (393 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (325953943 / 1000000000) ≤ -Real.log (5120 / 7093) ∧
    -Real.log (5120 / 7093) ≤ (40744243 / 125000000) := by
  have h := checkLog_sound (w := (1973 / 12213)) (n := 12)
    (lo := (325953943 / 1000000000)) (hi := (40744243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7093 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7093 / 5120) = 1/(5120 / 7093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (325953943 / 1000000000) (40744243 / 125000000) (Real.log (7093 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7093 / 5120) = -Real.log (5120 / 7093) := by
    rw [show ((7093 / 5120) : ℝ) = ((5120 / 7093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (24335241 / 50000000) ≤ -Real.log (3147 / 5120) ∧
    -Real.log (3147 / 5120) ≤ (486704821 / 1000000000) := by
  have h := checkLog_sound (w := (1973 / 8267)) (n := 12)
    (lo := (24335241 / 50000000)) (hi := (486704821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3147) = 1/(3147 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-486704821 / 1000000000) (-24335241 / 50000000) (Real.log (3147 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (242383667 / 1000000000) ≤ -Real.log (1000000 / 1274283) ∧
    -Real.log (1000000 / 1274283) ≤ (60595917 / 250000000) := by
  have h := checkLog_sound (w := (274283 / 2274283)) (n := 12)
    (lo := (242383667 / 1000000000)) (hi := (60595917 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274283 / 1000000) = 1/(1000000 / 1274283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (242383667 / 1000000000) (60595917 / 250000000) (Real.log (1274283 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1274283 / 1000000) = -Real.log (1000000 / 1274283) := by
    rw [show ((1274283 / 1000000) : ℝ) = ((1000000 / 1274283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (320595147 / 1000000000) ≤ -Real.log (725717 / 1000000) ∧
    -Real.log (725717 / 1000000) ≤ (80148787 / 250000000) := by
  have h := checkLog_sound (w := (274283 / 1725717)) (n := 12)
    (lo := (320595147 / 1000000000)) (hi := (80148787 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 725717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 725717) = 1/(725717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-80148787 / 250000000) (-320595147 / 1000000000) (Real.log (725717 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (60679087 / 250000000) ≤ -Real.log (1000000 / 1274707) ∧
    -Real.log (1000000 / 1274707) ≤ (242716349 / 1000000000) := by
  have h := checkLog_sound (w := (274707 / 2274707)) (n := 12)
    (lo := (60679087 / 250000000)) (hi := (242716349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274707 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274707 / 1000000) = 1/(1000000 / 1274707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (60679087 / 250000000) (242716349 / 1000000000) (Real.log (1274707 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1274707 / 1000000) = -Real.log (1000000 / 1274707) := by
    rw [show ((1274707 / 1000000) : ℝ) = ((1000000 / 1274707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (321179567 / 1000000000) ≤ -Real.log (725293 / 1000000) ∧
    -Real.log (725293 / 1000000) ≤ (20073723 / 62500000) := by
  have h := checkLog_sound (w := (274707 / 1725293)) (n := 12)
    (lo := (321179567 / 1000000000)) (hi := (20073723 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 725293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 725293) = 1/(725293 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20073723 / 62500000) (-321179567 / 1000000000) (Real.log (725293 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (180715267 / 1000000000) ≤ -Real.log (500000 / 599037) ∧
    -Real.log (500000 / 599037) ≤ (45178817 / 250000000) := by
  have h := checkLog_sound (w := (99037 / 1099037)) (n := 12)
    (lo := (180715267 / 1000000000)) (hi := (45178817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599037 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599037 / 500000) = 1/(500000 / 599037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (180715267 / 1000000000) (45178817 / 250000000) (Real.log (599037 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (599037 / 500000) = -Real.log (500000 / 599037) := by
    rw [show ((599037 / 500000) : ℝ) = ((500000 / 599037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1724523 / 7812500) ≤ -Real.log (400963 / 500000) ∧
    -Real.log (400963 / 500000) ≤ (44147789 / 200000000) := by
  have h := checkLog_sound (w := (99037 / 900963)) (n := 12)
    (lo := (1724523 / 7812500)) (hi := (44147789 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400963) = 1/(400963 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-44147789 / 200000000) (-1724523 / 7812500) (Real.log (400963 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (180982327 / 1000000000) ≤ -Real.log (500000 / 599197) ∧
    -Real.log (500000 / 599197) ≤ (22622791 / 125000000) := by
  have h := checkLog_sound (w := (99197 / 1099197)) (n := 12)
    (lo := (180982327 / 1000000000)) (hi := (22622791 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599197 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599197 / 500000) = 1/(500000 / 599197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (180982327 / 1000000000) (22622791 / 125000000) (Real.log (599197 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (599197 / 500000) = -Real.log (500000 / 599197) := by
    rw [show ((599197 / 500000) : ℝ) = ((500000 / 599197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (221138063 / 1000000000) ≤ -Real.log (400803 / 500000) ∧
    -Real.log (400803 / 500000) ≤ (13821129 / 62500000) := by
  have h := checkLog_sound (w := (99197 / 900803)) (n := 12)
    (lo := (221138063 / 1000000000)) (hi := (13821129 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400803) = 1/(400803 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-13821129 / 62500000) (-221138063 / 1000000000) (Real.log (400803 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (812658763 / 1000000000) ≤ -Real.log (500000000000 / 1126946298061) ∧
    -Real.log (500000000000 / 1126946298061) ≤ (162531753 / 200000000) := by
  have h := checkLog_sound (w := (126946298061 / 2126946298061)) (n := 12)
    (lo := (119511583 / 1000000000)) (hi := (3734737 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126946298061 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1126946298061 / 1000000000000) = 1/(500000000000 / 1126946298061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (812658763 / 1000000000) (162531753 / 200000000) (Real.log (1126946298061 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1126946298061 / 500000000000) = -Real.log (500000000000 / 1126946298061) := by
    rw [show ((1126946298061 / 500000000000) : ℝ) = ((500000000000 / 1126946298061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (814035369 / 1000000000) ≤ -Real.log (62500000000 / 141062340967) ∧
    -Real.log (62500000000 / 141062340967) ≤ (814035371 / 1000000000) := by
  have h := checkLog_sound (w := (16062340967 / 266062340967)) (n := 12)
    (lo := (120888189 / 1000000000)) (hi := (12088819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141062340967 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(141062340967 / 125000000000) = 1/(62500000000 / 141062340967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (814035369 / 1000000000) (814035371 / 1000000000) (Real.log (141062340967 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (141062340967 / 62500000000) = -Real.log (62500000000 / 141062340967) := by
    rw [show ((141062340967 / 62500000000) : ℝ) = ((62500000000 / 141062340967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (281489407 / 500000000) ≤ -Real.log (125000000000 / 219486900541) ∧
    -Real.log (125000000000 / 219486900541) ≤ (112595763 / 200000000) := by
  have h := checkLog_sound (w := (94486900541 / 344486900541)) (n := 12)
    (lo := (281489407 / 500000000)) (hi := (112595763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219486900541 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219486900541 / 125000000000) = 1/(125000000000 / 219486900541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (281489407 / 500000000) (112595763 / 200000000) (Real.log (219486900541 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (219486900541 / 125000000000) = -Real.log (125000000000 / 219486900541) := by
    rw [show ((219486900541 / 125000000000) : ℝ) = ((125000000000 / 219486900541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (140973979 / 250000000) ≤ -Real.log (500000000000 / 878753138387) ∧
    -Real.log (500000000000 / 878753138387) ≤ (563895917 / 1000000000) := by
  have h := checkLog_sound (w := (378753138387 / 1378753138387)) (n := 12)
    (lo := (140973979 / 250000000)) (hi := (563895917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((878753138387 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(878753138387 / 500000000000) = 1/(500000000000 / 878753138387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (140973979 / 250000000) (563895917 / 1000000000) (Real.log (878753138387 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (878753138387 / 500000000000) = -Real.log (500000000000 / 878753138387) := by
    rw [show ((878753138387 / 500000000000) : ℝ) = ((500000000000 / 878753138387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (100363553 / 250000000) ≤ -Real.log (500000000000 / 746997852669) ∧
    -Real.log (500000000000 / 746997852669) ≤ (401454213 / 1000000000) := by
  have h := checkLog_sound (w := (246997852669 / 1246997852669)) (n := 12)
    (lo := (100363553 / 250000000)) (hi := (401454213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746997852669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746997852669 / 500000000000) = 1/(500000000000 / 746997852669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (100363553 / 250000000) (401454213 / 1000000000) (Real.log (746997852669 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (746997852669 / 500000000000) = -Real.log (500000000000 / 746997852669) := by
    rw [show ((746997852669 / 500000000000) : ℝ) = ((500000000000 / 746997852669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (40212039 / 100000000) ≤ -Real.log (250000000000 / 373747826239) ∧
    -Real.log (250000000000 / 373747826239) ≤ (402120391 / 1000000000) := by
  have h := checkLog_sound (w := (123747826239 / 623747826239)) (n := 12)
    (lo := (40212039 / 100000000)) (hi := (402120391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373747826239 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373747826239 / 250000000000) = 1/(250000000000 / 373747826239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (40212039 / 100000000) (402120391 / 1000000000) (Real.log (373747826239 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (373747826239 / 250000000000) = -Real.log (250000000000 / 373747826239) := by
    rw [show ((373747826239 / 250000000000) : ℝ) = ((250000000000 / 373747826239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5019467 / 125000000) ≤ -Real.log (240159955191 / 250000000000) ∧
    -Real.log (240159955191 / 250000000000) ≤ (40155737 / 1000000000) := by
  have h := checkLog_sound (w := (9840044809 / 490159955191)) (n := 12)
    (lo := (5019467 / 125000000)) (hi := (40155737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240159955191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240159955191) = 1/(240159955191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40155737 / 1000000000) (-5019467 / 125000000) (Real.log (240159955191 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40023677 / 1000000000) ≤ -Real.log (240191672631 / 250000000000) ∧
    -Real.log (240191672631 / 250000000000) ≤ (20011839 / 500000000) := by
  have h := checkLog_sound (w := (9808327369 / 490191672631)) (n := 12)
    (lo := (40023677 / 1000000000)) (hi := (20011839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240191672631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240191672631) = 1/(240191672631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20011839 / 500000000) (-40023677 / 1000000000) (Real.log (240191672631 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell231

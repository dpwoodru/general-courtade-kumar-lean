import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell233
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

theorem reflection_log_1_neg : (65444399 / 200000000) ≤ -Real.log (2560 / 3551) ∧
    -Real.log (2560 / 3551) ≤ (81805499 / 250000000) := by
  have h := checkLog_sound (w := (991 / 6111)) (n := 12)
    (lo := (65444399 / 200000000)) (hi := (81805499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3551 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3551 / 2560) = 1/(2560 / 3551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65444399 / 200000000) (81805499 / 250000000) (Real.log (3551 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3551 / 2560) = -Real.log (2560 / 3551) := by
    rw [show ((3551 / 2560) : ℝ) = ((2560 / 3551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (30598049 / 62500000) ≤ -Real.log (1569 / 2560) ∧
    -Real.log (1569 / 2560) ≤ (97913757 / 200000000) := by
  have h := checkLog_sound (w := (991 / 4129)) (n := 12)
    (lo := (30598049 / 62500000)) (hi := (97913757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1569) = 1/(1569 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-97913757 / 200000000) (-30598049 / 62500000) (Real.log (1569 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (32679949 / 100000000) ≤ -Real.log (5120 / 7099) ∧
    -Real.log (5120 / 7099) ≤ (326799491 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 12219)) (n := 12)
    (lo := (32679949 / 100000000)) (hi := (326799491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7099 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7099 / 5120) = 1/(5120 / 7099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (32679949 / 100000000) (326799491 / 1000000000) (Real.log (7099 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7099 / 5120) = -Real.log (5120 / 7099) := by
    rw [show ((7099 / 5120) : ℝ) = ((5120 / 7099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (244306609 / 500000000) ≤ -Real.log (3141 / 5120) ∧
    -Real.log (3141 / 5120) ≤ (488613219 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 8261)) (n := 12)
    (lo := (244306609 / 500000000)) (hi := (488613219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3141) = 1/(3141 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-488613219 / 1000000000) (-244306609 / 500000000) (Real.log (3141 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (243047349 / 1000000000) ≤ -Real.log (1000000 / 1275129) ∧
    -Real.log (1000000 / 1275129) ≤ (4860947 / 20000000) := by
  have h := checkLog_sound (w := (275129 / 2275129)) (n := 12)
    (lo := (243047349 / 1000000000)) (hi := (4860947 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275129 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275129 / 1000000) = 1/(1000000 / 1275129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (243047349 / 1000000000) (4860947 / 20000000) (Real.log (1275129 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1275129 / 1000000) = -Real.log (1000000 / 1275129) := by
    rw [show ((1275129 / 1000000) : ℝ) = ((1000000 / 1275129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (32176157 / 100000000) ≤ -Real.log (724871 / 1000000) ∧
    -Real.log (724871 / 1000000) ≤ (321761571 / 1000000000) := by
  have h := checkLog_sound (w := (275129 / 1724871)) (n := 12)
    (lo := (32176157 / 100000000)) (hi := (321761571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 724871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 724871) = 1/(724871 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-321761571 / 1000000000) (-32176157 / 100000000) (Real.log (724871 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (24337981 / 100000000) ≤ -Real.log (1000000 / 1275553) ∧
    -Real.log (1000000 / 1275553) ≤ (243379811 / 1000000000) := by
  have h := checkLog_sound (w := (275553 / 2275553)) (n := 12)
    (lo := (24337981 / 100000000)) (hi := (243379811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275553 / 1000000) = 1/(1000000 / 1275553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (24337981 / 100000000) (243379811 / 1000000000) (Real.log (1275553 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1275553 / 1000000) = -Real.log (1000000 / 1275553) := by
    rw [show ((1275553 / 1000000) : ℝ) = ((1000000 / 1275553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (322346673 / 1000000000) ≤ -Real.log (724447 / 1000000) ∧
    -Real.log (724447 / 1000000) ≤ (161173337 / 500000000) := by
  have h := checkLog_sound (w := (275553 / 1724447)) (n := 12)
    (lo := (322346673 / 1000000000)) (hi := (161173337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 724447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 724447) = 1/(724447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-161173337 / 500000000) (-322346673 / 1000000000) (Real.log (724447 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (45311703 / 250000000) ≤ -Real.log (1000000 / 1198711) ∧
    -Real.log (1000000 / 1198711) ≤ (181246813 / 1000000000) := by
  have h := checkLog_sound (w := (198711 / 2198711)) (n := 12)
    (lo := (45311703 / 250000000)) (hi := (181246813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198711 / 1000000) = 1/(1000000 / 1198711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (45311703 / 250000000) (181246813 / 1000000000) (Real.log (1198711 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1198711 / 1000000) = -Real.log (1000000 / 1198711) := by
    rw [show ((1198711 / 1000000) : ℝ) = ((1000000 / 1198711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (221533597 / 1000000000) ≤ -Real.log (801289 / 1000000) ∧
    -Real.log (801289 / 1000000) ≤ (110766799 / 500000000) := by
  have h := checkLog_sound (w := (198711 / 1801289)) (n := 12)
    (lo := (221533597 / 1000000000)) (hi := (110766799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801289) = 1/(801289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-110766799 / 500000000) (-221533597 / 1000000000) (Real.log (801289 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (18151373 / 100000000) ≤ -Real.log (1000000 / 1199031) ∧
    -Real.log (1000000 / 1199031) ≤ (181513731 / 1000000000) := by
  have h := checkLog_sound (w := (199031 / 2199031)) (n := 12)
    (lo := (18151373 / 100000000)) (hi := (181513731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199031 / 1000000) = 1/(1000000 / 1199031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (18151373 / 100000000) (181513731 / 1000000000) (Real.log (1199031 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1199031 / 1000000) = -Real.log (1000000 / 1199031) := by
    rw [show ((1199031 / 1000000) : ℝ) = ((1000000 / 1199031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (110966517 / 500000000) ≤ -Real.log (800969 / 1000000) ∧
    -Real.log (800969 / 1000000) ≤ (44386607 / 200000000) := by
  have h := checkLog_sound (w := (199031 / 1800969)) (n := 12)
    (lo := (110966517 / 500000000)) (hi := (44386607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800969) = 1/(800969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-44386607 / 200000000) (-110966517 / 500000000) (Real.log (800969 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (815412707 / 1000000000) ≤ -Real.log (50000000000 / 113005412289) ∧
    -Real.log (50000000000 / 113005412289) ≤ (815412709 / 1000000000) := by
  have h := checkLog_sound (w := (13005412289 / 213005412289)) (n := 12)
    (lo := (122265527 / 1000000000)) (hi := (15283191 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113005412289 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(113005412289 / 100000000000) = 1/(50000000000 / 113005412289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (815412707 / 1000000000) (815412709 / 1000000000) (Real.log (113005412289 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (113005412289 / 50000000000) = -Real.log (50000000000 / 113005412289) := by
    rw [show ((113005412289 / 50000000000) : ℝ) = ((50000000000 / 113005412289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (816790779 / 1000000000) ≤ -Real.log (250000000000 / 565806246017) ∧
    -Real.log (250000000000 / 565806246017) ≤ (816790781 / 1000000000) := by
  have h := checkLog_sound (w := (65806246017 / 1065806246017)) (n := 12)
    (lo := (123643599 / 1000000000)) (hi := (309109 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565806246017 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(565806246017 / 500000000000) = 1/(250000000000 / 565806246017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (816790779 / 1000000000) (816790781 / 1000000000) (Real.log (565806246017 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (565806246017 / 250000000000) = -Real.log (250000000000 / 565806246017) := by
    rw [show ((565806246017 / 250000000000) : ℝ) = ((250000000000 / 565806246017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (14120223 / 25000000) ≤ -Real.log (25000000000 / 43977790531) ∧
    -Real.log (25000000000 / 43977790531) ≤ (564808921 / 1000000000) := by
  have h := checkLog_sound (w := (18977790531 / 68977790531)) (n := 12)
    (lo := (14120223 / 25000000)) (hi := (564808921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43977790531 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43977790531 / 25000000000) = 1/(25000000000 / 43977790531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14120223 / 25000000) (564808921 / 1000000000) (Real.log (43977790531 / 25000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (43977790531 / 25000000000) = -Real.log (25000000000 / 43977790531) := by
    rw [show ((43977790531 / 25000000000) : ℝ) = ((25000000000 / 43977790531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (565726483 / 1000000000) ≤ -Real.log (500000000000 / 880363228781) ∧
    -Real.log (500000000000 / 880363228781) ≤ (141431621 / 250000000) := by
  have h := checkLog_sound (w := (380363228781 / 1380363228781)) (n := 12)
    (lo := (565726483 / 1000000000)) (hi := (141431621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((880363228781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(880363228781 / 500000000000) = 1/(500000000000 / 880363228781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (565726483 / 1000000000) (141431621 / 250000000) (Real.log (880363228781 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (880363228781 / 500000000000) = -Real.log (500000000000 / 880363228781) := by
    rw [show ((880363228781 / 500000000000) : ℝ) = ((500000000000 / 880363228781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (40278041 / 100000000) ≤ -Real.log (500000000000 / 747989177437) ∧
    -Real.log (500000000000 / 747989177437) ≤ (402780411 / 1000000000) := by
  have h := checkLog_sound (w := (247989177437 / 1247989177437)) (n := 12)
    (lo := (40278041 / 100000000)) (hi := (402780411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747989177437 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747989177437 / 500000000000) = 1/(500000000000 / 747989177437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (40278041 / 100000000) (402780411 / 1000000000) (Real.log (747989177437 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (747989177437 / 500000000000) = -Real.log (500000000000 / 747989177437) := by
    rw [show ((747989177437 / 500000000000) : ℝ) = ((500000000000 / 747989177437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (100861691 / 250000000) ≤ -Real.log (50000000000 / 74848776919) ∧
    -Real.log (50000000000 / 74848776919) ≤ (80689353 / 200000000) := by
  have h := checkLog_sound (w := (24848776919 / 124848776919)) (n := 12)
    (lo := (100861691 / 250000000)) (hi := (80689353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74848776919 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74848776919 / 50000000000) = 1/(50000000000 / 74848776919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (100861691 / 250000000) (80689353 / 200000000) (Real.log (74848776919 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (74848776919 / 50000000000) = -Real.log (50000000000 / 74848776919) := by
    rw [show ((74848776919 / 50000000000) : ℝ) = ((50000000000 / 74848776919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (40419303 / 1000000000) ≤ -Real.log (960386661039 / 1000000000000) ∧
    -Real.log (960386661039 / 1000000000000) ≤ (5052413 / 125000000) := by
  have h := checkLog_sound (w := (39613338961 / 1960386661039)) (n := 12)
    (lo := (40419303 / 1000000000)) (hi := (5052413 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960386661039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960386661039) = 1/(960386661039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5052413 / 125000000) (-40419303 / 1000000000) (Real.log (960386661039 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8057357 / 200000000) ≤ -Real.log (960513938479 / 1000000000000) ∧
    -Real.log (960513938479 / 1000000000000) ≤ (20143393 / 500000000) := by
  have h := checkLog_sound (w := (39486061521 / 1960513938479)) (n := 12)
    (lo := (8057357 / 200000000)) (hi := (20143393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960513938479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960513938479) = 1/(960513938479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20143393 / 500000000) (-8057357 / 200000000) (Real.log (960513938479 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell233

import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell122
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

theorem reflection_log_1_neg : (139599463 / 500000000) ≤ -Real.log (5120 / 6769) ∧
    -Real.log (5120 / 6769) ≤ (279198927 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 11889)) (n := 12)
    (lo := (139599463 / 500000000)) (hi := (279198927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6769 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6769 / 5120) = 1/(5120 / 6769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (139599463 / 500000000) (279198927 / 1000000000) (Real.log (6769 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6769 / 5120) = -Real.log (5120 / 6769) := by
    rw [show ((6769 / 5120) : ℝ) = ((5120 / 6769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (194355851 / 500000000) ≤ -Real.log (3471 / 5120) ∧
    -Real.log (3471 / 5120) ≤ (388711703 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 8591)) (n := 12)
    (lo := (194355851 / 500000000)) (hi := (388711703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3471) = 1/(3471 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-388711703 / 1000000000) (-194355851 / 500000000) (Real.log (3471 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (278755631 / 1000000000) ≤ -Real.log (2560 / 3383) ∧
    -Real.log (2560 / 3383) ≤ (17422227 / 62500000) := by
  have h := checkLog_sound (w := (823 / 5943)) (n := 12)
    (lo := (278755631 / 1000000000)) (hi := (17422227 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3383 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3383 / 2560) = 1/(2560 / 3383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (278755631 / 1000000000) (17422227 / 62500000) (Real.log (3383 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3383 / 2560) = -Real.log (2560 / 3383) := by
    rw [show ((3383 / 2560) : ℝ) = ((2560 / 3383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (387847771 / 1000000000) ≤ -Real.log (1737 / 2560) ∧
    -Real.log (1737 / 2560) ≤ (96961943 / 250000000) := by
  have h := checkLog_sound (w := (823 / 4297)) (n := 12)
    (lo := (387847771 / 1000000000)) (hi := (96961943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1737) = 1/(1737 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-96961943 / 250000000) (-387847771 / 1000000000) (Real.log (1737 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (205669363 / 1000000000) ≤ -Real.log (1000000 / 1228347) ∧
    -Real.log (1000000 / 1228347) ≤ (51417341 / 250000000) := by
  have h := checkLog_sound (w := (228347 / 2228347)) (n := 12)
    (lo := (205669363 / 1000000000)) (hi := (51417341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228347 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228347 / 1000000) = 1/(1000000 / 1228347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (205669363 / 1000000000) (51417341 / 250000000) (Real.log (1228347 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1228347 / 1000000) = -Real.log (1000000 / 1228347) := by
    rw [show ((1228347 / 1000000) : ℝ) = ((1000000 / 1228347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (259220311 / 1000000000) ≤ -Real.log (771653 / 1000000) ∧
    -Real.log (771653 / 1000000) ≤ (32402539 / 125000000) := by
  have h := checkLog_sound (w := (228347 / 1771653)) (n := 12)
    (lo := (259220311 / 1000000000)) (hi := (32402539 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 771653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 771653) = 1/(771653 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-32402539 / 125000000) (-259220311 / 1000000000) (Real.log (771653 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (206012041 / 1000000000) ≤ -Real.log (31250 / 38399) ∧
    -Real.log (31250 / 38399) ≤ (103006021 / 500000000) := by
  have h := checkLog_sound (w := (7149 / 69649)) (n := 12)
    (lo := (206012041 / 1000000000)) (hi := (103006021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38399 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38399 / 31250) = 1/(31250 / 38399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (206012041 / 1000000000) (103006021 / 500000000) (Real.log (38399 / 31250)) := by
  have h := reflection_log_7_neg
  have he : Real.log (38399 / 31250) = -Real.log (31250 / 38399) := by
    rw [show ((38399 / 31250) : ℝ) = ((31250 / 38399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (129883021 / 500000000) ≤ -Real.log (24101 / 31250) ∧
    -Real.log (24101 / 31250) ≤ (259766043 / 1000000000) := by
  have h := checkLog_sound (w := (7149 / 55351)) (n := 12)
    (lo := (129883021 / 500000000)) (hi := (259766043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24101) = 1/(24101 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-259766043 / 1000000000) (-129883021 / 500000000) (Real.log (24101 / 31250)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18964751 / 125000000) ≤ -Real.log (125000 / 145479) ∧
    -Real.log (125000 / 145479) ≤ (151718009 / 1000000000) := by
  have h := checkLog_sound (w := (20479 / 270479)) (n := 12)
    (lo := (18964751 / 125000000)) (hi := (151718009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145479 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145479 / 125000) = 1/(125000 / 145479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18964751 / 125000000) (151718009 / 1000000000) (Real.log (145479 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (145479 / 125000) = -Real.log (125000 / 145479) := by
    rw [show ((145479 / 125000) : ℝ) = ((125000 / 145479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (178925729 / 1000000000) ≤ -Real.log (104521 / 125000) ∧
    -Real.log (104521 / 125000) ≤ (17892573 / 100000000) := by
  have h := checkLog_sound (w := (20479 / 229521)) (n := 12)
    (lo := (178925729 / 1000000000)) (hi := (17892573 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104521) = 1/(104521 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-17892573 / 100000000) (-178925729 / 1000000000) (Real.log (104521 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37996513 / 250000000) ≤ -Real.log (62500 / 72759) ∧
    -Real.log (62500 / 72759) ≤ (151986053 / 1000000000) := by
  have h := checkLog_sound (w := (10259 / 135259)) (n := 12)
    (lo := (37996513 / 250000000)) (hi := (151986053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72759 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72759 / 62500) = 1/(62500 / 72759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37996513 / 250000000) (151986053 / 1000000000) (Real.log (72759 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (72759 / 62500) = -Real.log (62500 / 72759) := by
    rw [show ((72759 / 62500) : ℝ) = ((62500 / 72759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (179298929 / 1000000000) ≤ -Real.log (52241 / 62500) ∧
    -Real.log (52241 / 62500) ≤ (17929893 / 100000000) := by
  have h := checkLog_sound (w := (10259 / 114741)) (n := 12)
    (lo := (179298929 / 1000000000)) (hi := (17929893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 52241) = 1/(52241 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-17929893 / 100000000) (-179298929 / 1000000000) (Real.log (52241 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (333301701 / 500000000) ≤ -Real.log (500000000000 / 973805411629) ∧
    -Real.log (500000000000 / 973805411629) ≤ (666603403 / 1000000000) := by
  have h := checkLog_sound (w := (473805411629 / 1473805411629)) (n := 12)
    (lo := (333301701 / 500000000)) (hi := (666603403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973805411629 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973805411629 / 500000000000) = 1/(500000000000 / 973805411629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (333301701 / 500000000) (666603403 / 1000000000) (Real.log (973805411629 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (973805411629 / 500000000000) = -Real.log (500000000000 / 973805411629) := by
    rw [show ((973805411629 / 500000000000) : ℝ) = ((500000000000 / 973805411629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (166977657 / 250000000) ≤ -Real.log (500000000000 / 975079227889) ∧
    -Real.log (500000000000 / 975079227889) ≤ (667910629 / 1000000000) := by
  have h := checkLog_sound (w := (475079227889 / 1475079227889)) (n := 12)
    (lo := (166977657 / 250000000)) (hi := (667910629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((975079227889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(975079227889 / 500000000000) = 1/(500000000000 / 975079227889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (166977657 / 250000000) (667910629 / 1000000000) (Real.log (975079227889 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (975079227889 / 500000000000) = -Real.log (500000000000 / 975079227889) := by
    rw [show ((975079227889 / 500000000000) : ℝ) = ((500000000000 / 975079227889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (232444837 / 500000000) ≤ -Real.log (500000000000 / 795919279779) ∧
    -Real.log (500000000000 / 795919279779) ≤ (18595587 / 40000000) := by
  have h := checkLog_sound (w := (295919279779 / 1295919279779)) (n := 12)
    (lo := (232444837 / 500000000)) (hi := (18595587 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795919279779 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795919279779 / 500000000000) = 1/(500000000000 / 795919279779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (232444837 / 500000000) (18595587 / 40000000) (Real.log (795919279779 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (795919279779 / 500000000000) = -Real.log (500000000000 / 795919279779) := by
    rw [show ((795919279779 / 500000000000) : ℝ) = ((500000000000 / 795919279779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (116444521 / 250000000) ≤ -Real.log (125000000000 / 199156673997) ∧
    -Real.log (125000000000 / 199156673997) ≤ (93155617 / 200000000) := by
  have h := checkLog_sound (w := (74156673997 / 324156673997)) (n := 12)
    (lo := (116444521 / 250000000)) (hi := (93155617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199156673997 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199156673997 / 125000000000) = 1/(125000000000 / 199156673997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (116444521 / 250000000) (93155617 / 200000000) (Real.log (199156673997 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (199156673997 / 125000000000) = -Real.log (125000000000 / 199156673997) := by
    rw [show ((199156673997 / 125000000000) : ℝ) = ((125000000000 / 199156673997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (165321869 / 500000000) ≤ -Real.log (500000000000 / 695931917987) ∧
    -Real.log (500000000000 / 695931917987) ≤ (330643739 / 1000000000) := by
  have h := checkLog_sound (w := (195931917987 / 1195931917987)) (n := 12)
    (lo := (165321869 / 500000000)) (hi := (330643739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695931917987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695931917987 / 500000000000) = 1/(500000000000 / 695931917987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (165321869 / 500000000) (330643739 / 1000000000) (Real.log (695931917987 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (695931917987 / 500000000000) = -Real.log (500000000000 / 695931917987) := by
    rw [show ((695931917987 / 500000000000) : ℝ) = ((500000000000 / 695931917987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (165642491 / 500000000) ≤ -Real.log (500000000000 / 696378323539) ∧
    -Real.log (500000000000 / 696378323539) ≤ (331284983 / 1000000000) := by
  have h := checkLog_sound (w := (196378323539 / 1196378323539)) (n := 12)
    (lo := (165642491 / 500000000)) (hi := (331284983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696378323539 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696378323539 / 500000000000) = 1/(500000000000 / 696378323539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (165642491 / 500000000) (331284983 / 1000000000) (Real.log (696378323539 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (696378323539 / 500000000000) = -Real.log (500000000000 / 696378323539) := by
    rw [show ((696378323539 / 500000000000) : ℝ) = ((500000000000 / 696378323539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6828219 / 250000000) ≤ -Real.log (3801002919 / 3906250000) ∧
    -Real.log (3801002919 / 3906250000) ≤ (27312877 / 1000000000) := by
  have h := checkLog_sound (w := (105247081 / 7707252919)) (n := 12)
    (lo := (6828219 / 250000000)) (hi := (27312877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3801002919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3801002919) = 1/(3801002919 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-27312877 / 1000000000) (-6828219 / 250000000) (Real.log (3801002919 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (680193 / 25000000) ≤ -Real.log (15205610559 / 15625000000) ∧
    -Real.log (15205610559 / 15625000000) ≤ (27207721 / 1000000000) := by
  have h := checkLog_sound (w := (419389441 / 30830610559)) (n := 12)
    (lo := (680193 / 25000000)) (hi := (27207721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15205610559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15205610559) = 1/(15205610559 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-27207721 / 1000000000) (-680193 / 25000000) (Real.log (15205610559 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell122

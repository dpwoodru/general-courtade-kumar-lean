import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell159
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

theorem reflection_log_1_neg : (73866053 / 250000000) ≤ -Real.log (32 / 43) ∧
    -Real.log (32 / 43) ≤ (295464213 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 75)) (n := 12)
    (lo := (73866053 / 250000000)) (hi := (295464213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43 / 32) = 1/(32 / 43) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (73866053 / 250000000) (295464213 / 1000000000) (Real.log (43 / 32)) := by
  have h := reflection_log_1_neg
  have he : Real.log (43 / 32) = -Real.log (32 / 43) := by
    rw [show ((43 / 32) : ℝ) = ((32 / 43) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (84242693 / 200000000) ≤ -Real.log (21 / 32) ∧
    -Real.log (21 / 32) ≤ (210606733 / 500000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 21) = 1/(21 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-210606733 / 500000000) (-84242693 / 200000000) (Real.log (21 / 32)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (295028071 / 1000000000) ≤ -Real.log (5120 / 6877) ∧
    -Real.log (5120 / 6877) ≤ (36878509 / 125000000) := by
  have h := checkLog_sound (w := (1757 / 11997)) (n := 12)
    (lo := (295028071 / 1000000000)) (hi := (36878509 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6877 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6877 / 5120) = 1/(5120 / 6877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (295028071 / 1000000000) (36878509 / 125000000) (Real.log (6877 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6877 / 5120) = -Real.log (5120 / 6877) := by
    rw [show ((6877 / 5120) : ℝ) = ((5120 / 6877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (210160503 / 500000000) ≤ -Real.log (3363 / 5120) ∧
    -Real.log (3363 / 5120) ≤ (420321007 / 1000000000) := by
  have h := checkLog_sound (w := (1757 / 8483)) (n := 12)
    (lo := (210160503 / 500000000)) (hi := (420321007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3363) = 1/(3363 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-420321007 / 1000000000) (-210160503 / 500000000) (Real.log (3363 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (54564107 / 250000000) ≤ -Real.log (500000 / 621953) ∧
    -Real.log (500000 / 621953) ≤ (218256429 / 1000000000) := by
  have h := checkLog_sound (w := (121953 / 1121953)) (n := 12)
    (lo := (54564107 / 250000000)) (hi := (218256429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621953 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621953 / 500000) = 1/(500000 / 621953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (54564107 / 250000000) (218256429 / 1000000000) (Real.log (621953 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (621953 / 500000) = -Real.log (500000 / 621953) := by
    rw [show ((621953 / 500000) : ℝ) = ((500000 / 621953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (279589571 / 1000000000) ≤ -Real.log (378047 / 500000) ∧
    -Real.log (378047 / 500000) ≤ (69897393 / 250000000) := by
  have h := checkLog_sound (w := (121953 / 878047)) (n := 12)
    (lo := (279589571 / 1000000000)) (hi := (69897393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378047) = 1/(378047 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-69897393 / 250000000) (-279589571 / 1000000000) (Real.log (378047 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (349753 / 1600000) ≤ -Real.log (125000 / 155541) ∧
    -Real.log (125000 / 155541) ≤ (109297813 / 500000000) := by
  have h := checkLog_sound (w := (30541 / 280541)) (n := 12)
    (lo := (349753 / 1600000)) (hi := (109297813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155541 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155541 / 125000) = 1/(125000 / 155541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (349753 / 1600000) (109297813 / 500000000) (Real.log (155541 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (155541 / 125000) = -Real.log (125000 / 155541) := by
    rw [show ((155541 / 125000) : ℝ) = ((125000 / 155541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (280147859 / 1000000000) ≤ -Real.log (94459 / 125000) ∧
    -Real.log (94459 / 125000) ≤ (14007393 / 50000000) := by
  have h := checkLog_sound (w := (30541 / 219459)) (n := 12)
    (lo := (280147859 / 1000000000)) (hi := (14007393 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94459) = 1/(94459 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-14007393 / 50000000) (-280147859 / 1000000000) (Real.log (94459 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (161571931 / 1000000000) ≤ -Real.log (1000000 / 1175357) ∧
    -Real.log (1000000 / 1175357) ≤ (40392983 / 250000000) := by
  have h := checkLog_sound (w := (175357 / 2175357)) (n := 12)
    (lo := (161571931 / 1000000000)) (hi := (40392983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1175357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1175357 / 1000000) = 1/(1000000 / 1175357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (161571931 / 1000000000) (40392983 / 250000000) (Real.log (1175357 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1175357 / 1000000) = -Real.log (1000000 / 1175357) := by
    rw [show ((1175357 / 1000000) : ℝ) = ((1000000 / 1175357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (192804713 / 1000000000) ≤ -Real.log (824643 / 1000000) ∧
    -Real.log (824643 / 1000000) ≤ (96402357 / 500000000) := by
  have h := checkLog_sound (w := (175357 / 1824643)) (n := 12)
    (lo := (192804713 / 1000000000)) (hi := (96402357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 824643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 824643) = 1/(824643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-96402357 / 500000000) (-192804713 / 1000000000) (Real.log (824643 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20229881 / 125000000) ≤ -Real.log (1000000 / 1175671) ∧
    -Real.log (1000000 / 1175671) ≤ (161839049 / 1000000000) := by
  have h := checkLog_sound (w := (175671 / 2175671)) (n := 12)
    (lo := (20229881 / 125000000)) (hi := (161839049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1175671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1175671 / 1000000) = 1/(1000000 / 1175671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20229881 / 125000000) (161839049 / 1000000000) (Real.log (1175671 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1175671 / 1000000) = -Real.log (1000000 / 1175671) := by
    rw [show ((1175671 / 1000000) : ℝ) = ((1000000 / 1175671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (48296389 / 250000000) ≤ -Real.log (824329 / 1000000) ∧
    -Real.log (824329 / 1000000) ≤ (193185557 / 1000000000) := by
  have h := checkLog_sound (w := (175671 / 1824329)) (n := 12)
    (lo := (48296389 / 250000000)) (hi := (193185557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 824329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 824329) = 1/(824329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-193185557 / 1000000000) (-48296389 / 250000000) (Real.log (824329 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (715349077 / 1000000000) ≤ -Real.log (500000000000 / 1022450193279) ∧
    -Real.log (500000000000 / 1022450193279) ≤ (715349079 / 1000000000) := by
  have h := checkLog_sound (w := (22450193279 / 2022450193279)) (n := 12)
    (lo := (22201897 / 1000000000)) (hi := (11100949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1022450193279 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1022450193279 / 1000000000000) = 1/(500000000000 / 1022450193279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (715349077 / 1000000000) (715349079 / 1000000000) (Real.log (1022450193279 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1022450193279 / 500000000000) = -Real.log (500000000000 / 1022450193279) := by
    rw [show ((1022450193279 / 500000000000) : ℝ) = ((500000000000 / 1022450193279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (716677677 / 1000000000) ≤ -Real.log (50000000000 / 102380952381) ∧
    -Real.log (50000000000 / 102380952381) ≤ (716677679 / 1000000000) := by
  have h := checkLog_sound (w := (2380952381 / 202380952381)) (n := 12)
    (lo := (23530497 / 1000000000)) (hi := (11765249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102380952381 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102380952381 / 100000000000) = 1/(50000000000 / 102380952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (716677677 / 1000000000) (716677679 / 1000000000) (Real.log (102380952381 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (102380952381 / 50000000000) = -Real.log (50000000000 / 102380952381) := by
    rw [show ((102380952381 / 50000000000) : ℝ) = ((50000000000 / 102380952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (248923 / 500000) ≤ -Real.log (250000000000 / 411293437059) ∧
    -Real.log (250000000000 / 411293437059) ≤ (497846001 / 1000000000) := by
  have h := checkLog_sound (w := (161293437059 / 661293437059)) (n := 12)
    (lo := (248923 / 500000)) (hi := (497846001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411293437059 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411293437059 / 250000000000) = 1/(250000000000 / 411293437059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (248923 / 500000) (497846001 / 1000000000) (Real.log (411293437059 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (411293437059 / 250000000000) = -Real.log (250000000000 / 411293437059) := by
    rw [show ((411293437059 / 250000000000) : ℝ) = ((250000000000 / 411293437059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (124685871 / 250000000) ≤ -Real.log (250000000000 / 411662731979) ∧
    -Real.log (250000000000 / 411662731979) ≤ (99748697 / 200000000) := by
  have h := checkLog_sound (w := (161662731979 / 661662731979)) (n := 12)
    (lo := (124685871 / 250000000)) (hi := (99748697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411662731979 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411662731979 / 250000000000) = 1/(250000000000 / 411662731979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (124685871 / 250000000) (99748697 / 200000000) (Real.log (411662731979 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (411662731979 / 250000000000) = -Real.log (250000000000 / 411662731979) := by
    rw [show ((411662731979 / 250000000000) : ℝ) = ((250000000000 / 411662731979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (88594161 / 250000000) ≤ -Real.log (500000000000 / 712645957099) ∧
    -Real.log (500000000000 / 712645957099) ≤ (70875329 / 200000000) := by
  have h := checkLog_sound (w := (212645957099 / 1212645957099)) (n := 12)
    (lo := (88594161 / 250000000)) (hi := (70875329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712645957099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712645957099 / 500000000000) = 1/(500000000000 / 712645957099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (88594161 / 250000000) (70875329 / 200000000) (Real.log (712645957099 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (712645957099 / 500000000000) = -Real.log (500000000000 / 712645957099) := by
    rw [show ((712645957099 / 500000000000) : ℝ) = ((500000000000 / 712645957099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (71004921 / 200000000) ≤ -Real.log (62500000000 / 89138484149) ∧
    -Real.log (62500000000 / 89138484149) ≤ (177512303 / 500000000) := by
  have h := checkLog_sound (w := (26638484149 / 151638484149)) (n := 12)
    (lo := (71004921 / 200000000)) (hi := (177512303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89138484149 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89138484149 / 62500000000) = 1/(62500000000 / 89138484149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (71004921 / 200000000) (177512303 / 500000000) (Real.log (89138484149 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (89138484149 / 62500000000) = -Real.log (62500000000 / 89138484149) := by
    rw [show ((89138484149 / 62500000000) : ℝ) = ((62500000000 / 89138484149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7836627 / 250000000) ≤ -Real.log (969139699759 / 1000000000000) ∧
    -Real.log (969139699759 / 1000000000000) ≤ (31346509 / 1000000000) := by
  have h := checkLog_sound (w := (30860300241 / 1969139699759)) (n := 12)
    (lo := (7836627 / 250000000)) (hi := (31346509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969139699759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969139699759) = 1/(969139699759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31346509 / 1000000000) (-7836627 / 250000000) (Real.log (969139699759 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (15616391 / 500000000) ≤ -Real.log (969249922551 / 1000000000000) ∧
    -Real.log (969249922551 / 1000000000000) ≤ (31232783 / 1000000000) := by
  have h := checkLog_sound (w := (30750077449 / 1969249922551)) (n := 12)
    (lo := (15616391 / 500000000)) (hi := (31232783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969249922551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969249922551) = 1/(969249922551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-31232783 / 1000000000) (-15616391 / 500000000) (Real.log (969249922551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell159

import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0180
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

theorem reflection_log_1_neg : (54921741 / 200000000) ≤ -Real.log (2560 / 3369) ∧
    -Real.log (2560 / 3369) ≤ (137304353 / 500000000) := by
  have h := checkLog_sound (w := (809 / 5929)) (n := 12)
    (lo := (54921741 / 200000000)) (hi := (137304353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3369 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3369 / 2560) = 1/(2560 / 3369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (54921741 / 200000000) (137304353 / 500000000) (Real.log (3369 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3369 / 2560) = -Real.log (2560 / 3369) := by
    rw [show ((3369 / 2560) : ℝ) = ((2560 / 3369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (75964041 / 200000000) ≤ -Real.log (1751 / 2560) ∧
    -Real.log (1751 / 2560) ≤ (189910103 / 500000000) := by
  have h := checkLog_sound (w := (809 / 4311)) (n := 12)
    (lo := (75964041 / 200000000)) (hi := (189910103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1751) = 1/(1751 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-189910103 / 500000000) (-75964041 / 200000000) (Real.log (1751 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27416337 / 100000000) ≤ -Real.log (1024 / 1347) ∧
    -Real.log (1024 / 1347) ≤ (274163371 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 2371)) (n := 12)
    (lo := (27416337 / 100000000)) (hi := (274163371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1347 / 1024) = 1/(1024 / 1347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27416337 / 100000000) (274163371 / 1000000000) (Real.log (1347 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1347 / 1024) = -Real.log (1024 / 1347) := by
    rw [show ((1347 / 1024) : ℝ) = ((1024 / 1347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (189481959 / 500000000) ≤ -Real.log (701 / 1024) ∧
    -Real.log (701 / 1024) ≤ (378963919 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 1725)) (n := 12)
    (lo := (189481959 / 500000000)) (hi := (378963919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 701) = 1/(701 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-378963919 / 1000000000) (-189481959 / 500000000) (Real.log (701 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (122456351 / 250000000) ≤ -Real.log (1280 / 2089) ∧
    -Real.log (1280 / 2089) ≤ (97965081 / 200000000) := by
  have h := checkLog_sound (w := (809 / 3369)) (n := 12)
    (lo := (122456351 / 250000000)) (hi := (97965081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2089 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2089 / 1280) = 1/(1280 / 2089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (122456351 / 250000000) (97965081 / 200000000) (Real.log (2089 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2089 / 1280) = -Real.log (1280 / 2089) := by
    rw [show ((2089 / 1280) : ℝ) = ((1280 / 2089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (499878631 / 500000000) ≤ -Real.log (471 / 1280) ∧
    -Real.log (471 / 1280) ≤ (62484829 / 62500000) := by
  have h := checkLog_sound (w := (169 / 1111)) (n := 12)
    (lo := (153305041 / 500000000)) (hi := (306610083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 471) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 471) = 1/(471 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-62484829 / 62500000) (-499878631 / 500000000) (Real.log (471 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (489107099 / 1000000000) ≤ -Real.log (512 / 835) ∧
    -Real.log (512 / 835) ≤ (4891071 / 10000000) := by
  have h := checkLog_sound (w := (323 / 1347)) (n := 12)
    (lo := (489107099 / 1000000000)) (hi := (4891071 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835 / 512) = 1/(512 / 835) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (489107099 / 1000000000) (4891071 / 10000000) (Real.log (835 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (835 / 512) = -Real.log (512 / 835) := by
    rw [show ((835 / 512) : ℝ) = ((512 / 835) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (996577609 / 1000000000) ≤ -Real.log (189 / 512) ∧
    -Real.log (189 / 512) ≤ (996577611 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 445)) (n := 12)
    (lo := (303430429 / 1000000000)) (hi := (30343043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 189) = 1/(189 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-996577611 / 1000000000) (-996577609 / 1000000000) (Real.log (189 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (375046449 / 1000000000) ≤ -Real.log (1000000 / 1455059) ∧
    -Real.log (1000000 / 1455059) ≤ (7500929 / 20000000) := by
  have h := checkLog_sound (w := (455059 / 2455059)) (n := 12)
    (lo := (375046449 / 1000000000)) (hi := (7500929 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1455059 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1455059 / 1000000) = 1/(1000000 / 1455059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (375046449 / 1000000000) (7500929 / 20000000) (Real.log (1455059 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1455059 / 1000000) = -Real.log (1000000 / 1455059) := by
    rw [show ((1455059 / 1000000) : ℝ) = ((1000000 / 1455059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (607077747 / 1000000000) ≤ -Real.log (544941 / 1000000) ∧
    -Real.log (544941 / 1000000) ≤ (151769437 / 250000000) := by
  have h := checkLog_sound (w := (455059 / 1544941)) (n := 12)
    (lo := (607077747 / 1000000000)) (hi := (151769437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 544941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 544941) = 1/(544941 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-151769437 / 250000000) (-607077747 / 1000000000) (Real.log (544941 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (93914137 / 250000000) ≤ -Real.log (1000000 / 1455947) ∧
    -Real.log (1000000 / 1455947) ≤ (375656549 / 1000000000) := by
  have h := checkLog_sound (w := (455947 / 2455947)) (n := 12)
    (lo := (93914137 / 250000000)) (hi := (375656549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1455947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1455947 / 1000000) = 1/(1000000 / 1455947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (93914137 / 250000000) (375656549 / 1000000000) (Real.log (1455947 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1455947 / 1000000) = -Real.log (1000000 / 1455947) := by
    rw [show ((1455947 / 1000000) : ℝ) = ((1000000 / 1455947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (60870861 / 100000000) ≤ -Real.log (544053 / 1000000) ∧
    -Real.log (544053 / 1000000) ≤ (608708611 / 1000000000) := by
  have h := checkLog_sound (w := (455947 / 1544053)) (n := 12)
    (lo := (60870861 / 100000000)) (hi := (608708611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 544053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 544053) = 1/(544053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-608708611 / 1000000000) (-60870861 / 100000000) (Real.log (544053 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (146816291 / 500000000) ≤ -Real.log (1000000 / 1341291) ∧
    -Real.log (1000000 / 1341291) ≤ (293632583 / 1000000000) := by
  have h := checkLog_sound (w := (341291 / 2341291)) (n := 12)
    (lo := (146816291 / 500000000)) (hi := (293632583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341291 / 1000000) = 1/(1000000 / 1341291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (146816291 / 500000000) (293632583 / 1000000000) (Real.log (1341291 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1341291 / 1000000) = -Real.log (1000000 / 1341291) := by
    rw [show ((1341291 / 1000000) : ℝ) = ((1000000 / 1341291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (20873671 / 50000000) ≤ -Real.log (658709 / 1000000) ∧
    -Real.log (658709 / 1000000) ≤ (417473421 / 1000000000) := by
  have h := checkLog_sound (w := (341291 / 1658709)) (n := 12)
    (lo := (20873671 / 50000000)) (hi := (417473421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 658709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 658709) = 1/(658709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-417473421 / 1000000000) (-20873671 / 50000000) (Real.log (658709 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (4596697 / 15625000) ≤ -Real.log (1000000 / 1342037) ∧
    -Real.log (1000000 / 1342037) ≤ (294188609 / 1000000000) := by
  have h := checkLog_sound (w := (342037 / 2342037)) (n := 12)
    (lo := (4596697 / 15625000)) (hi := (294188609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1342037 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1342037 / 1000000) = 1/(1000000 / 1342037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4596697 / 15625000) (294188609 / 1000000000) (Real.log (1342037 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1342037 / 1000000) = -Real.log (1000000 / 1342037) := by
    rw [show ((1342037 / 1000000) : ℝ) = ((1000000 / 1342037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (20930329 / 50000000) ≤ -Real.log (657963 / 1000000) ∧
    -Real.log (657963 / 1000000) ≤ (418606581 / 1000000000) := by
  have h := checkLog_sound (w := (342037 / 1657963)) (n := 12)
    (lo := (20930329 / 50000000)) (hi := (418606581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 657963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 657963) = 1/(657963 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-418606581 / 1000000000) (-20930329 / 50000000) (Real.log (657963 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (245531049 / 250000000) ≤ -Real.log (100000000000 / 267012208661) ∧
    -Real.log (100000000000 / 267012208661) ≤ (491062099 / 500000000) := by
  have h := checkLog_sound (w := (67012208661 / 467012208661)) (n := 12)
    (lo := (36122127 / 125000000)) (hi := (288977017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267012208661 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(267012208661 / 200000000000) = 1/(100000000000 / 267012208661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (245531049 / 250000000) (491062099 / 500000000) (Real.log (267012208661 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (267012208661 / 100000000000) = -Real.log (100000000000 / 267012208661) := by
    rw [show ((267012208661 / 100000000000) : ℝ) = ((100000000000 / 267012208661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (984365157 / 1000000000) ≤ -Real.log (125000000000 / 334514054697) ∧
    -Real.log (125000000000 / 334514054697) ≤ (984365159 / 1000000000) := by
  have h := checkLog_sound (w := (84514054697 / 584514054697)) (n := 12)
    (lo := (291217977 / 1000000000)) (hi := (145608989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334514054697 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(334514054697 / 250000000000) = 1/(125000000000 / 334514054697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (984365157 / 1000000000) (984365159 / 1000000000) (Real.log (334514054697 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (334514054697 / 125000000000) = -Real.log (125000000000 / 334514054697) := by
    rw [show ((334514054697 / 125000000000) : ℝ) = ((125000000000 / 334514054697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (355553001 / 500000000) ≤ -Real.log (15625000000 / 31816282873) ∧
    -Real.log (15625000000 / 31816282873) ≤ (177776501 / 250000000) := by
  have h := checkLog_sound (w := (566282873 / 63066282873)) (n := 12)
    (lo := (8979411 / 500000000)) (hi := (17958823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31816282873 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31816282873 / 31250000000) = 1/(15625000000 / 31816282873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (355553001 / 500000000) (177776501 / 250000000) (Real.log (31816282873 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (31816282873 / 15625000000) = -Real.log (15625000000 / 31816282873) := by
    rw [show ((31816282873 / 15625000000) : ℝ) = ((15625000000 / 31816282873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (178198797 / 250000000) ≤ -Real.log (500000000000 / 1019842301163) ∧
    -Real.log (500000000000 / 1019842301163) ≤ (71279519 / 100000000) := by
  have h := checkLog_sound (w := (19842301163 / 2019842301163)) (n := 12)
    (lo := (2456001 / 125000000)) (hi := (19648009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1019842301163 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1019842301163 / 1000000000000) = 1/(500000000000 / 1019842301163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (178198797 / 250000000) (71279519 / 100000000) (Real.log (1019842301163 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1019842301163 / 500000000000) = -Real.log (500000000000 / 1019842301163) := by
    rw [show ((1019842301163 / 500000000000) : ℝ) = ((500000000000 / 1019842301163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0180

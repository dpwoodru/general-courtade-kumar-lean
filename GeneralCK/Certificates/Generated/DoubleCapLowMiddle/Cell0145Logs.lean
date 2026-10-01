import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0145
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

theorem reflection_log_1_neg : (164126877 / 250000000) ≤ -Real.log (12800 / 24679) ∧
    -Real.log (12800 / 24679) ≤ (656507509 / 1000000000) := by
  have h := checkLog_sound (w := (11879 / 37479)) (n := 12)
    (lo := (164126877 / 250000000)) (hi := (656507509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24679 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24679 / 12800) = 1/(12800 / 24679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (164126877 / 250000000) (656507509 / 1000000000) (Real.log (24679 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24679 / 12800) = -Real.log (12800 / 24679) := by
    rw [show ((24679 / 12800) : ℝ) = ((12800 / 24679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2631740411 / 1000000000) ≤ -Real.log (921 / 12800) ∧
    -Real.log (921 / 12800) ≤ (526348083 / 200000000) := by
  have h := checkLog_sound (w := (679 / 2521)) (n := 12)
    (lo := (552298871 / 1000000000)) (hi := (69037359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 921) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 921) = 1/(921 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-526348083 / 200000000) (-2631740411 / 1000000000) (Real.log (921 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (656122491 / 1000000000) ≤ -Real.log (25600 / 49339) ∧
    -Real.log (25600 / 49339) ≤ (164030623 / 250000000) := by
  have h := checkLog_sound (w := (23739 / 74939)) (n := 12)
    (lo := (656122491 / 1000000000)) (hi := (164030623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49339 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49339 / 25600) = 1/(25600 / 49339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (656122491 / 1000000000) (164030623 / 250000000) (Real.log (49339 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49339 / 25600) = -Real.log (25600 / 49339) := by
    rw [show ((49339 / 25600) : ℝ) = ((25600 / 49339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (655369593 / 250000000) ≤ -Real.log (1861 / 25600) ∧
    -Real.log (1861 / 25600) ≤ (327684797 / 125000000) := by
  have h := checkLog_sound (w := (1339 / 5061)) (n := 12)
    (lo := (16938651 / 31250000)) (hi := (542036833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1861) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1861) = 1/(1861 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-327684797 / 125000000) (-655369593 / 250000000) (Real.log (1861 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19327317 / 31250000) ≤ -Real.log (6400 / 11879) ∧
    -Real.log (6400 / 11879) ≤ (123694829 / 200000000) := by
  have h := checkLog_sound (w := (5479 / 18279)) (n := 12)
    (lo := (19327317 / 31250000)) (hi := (123694829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11879 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11879 / 6400) = 1/(6400 / 11879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19327317 / 31250000) (123694829 / 200000000) (Real.log (11879 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11879 / 6400) = -Real.log (6400 / 11879) := by
    rw [show ((11879 / 6400) : ℝ) = ((6400 / 11879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1938593231 / 1000000000) ≤ -Real.log (921 / 6400) ∧
    -Real.log (921 / 6400) ≤ (969296617 / 500000000) := by
  have h := checkLog_sound (w := (679 / 2521)) (n := 12)
    (lo := (552298871 / 1000000000)) (hi := (69037359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 921) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 921) = 1/(921 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-969296617 / 500000000) (-1938593231 / 1000000000) (Real.log (921 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (308837047 / 500000000) ≤ -Real.log (12800 / 23739) ∧
    -Real.log (12800 / 23739) ≤ (123534819 / 200000000) := by
  have h := checkLog_sound (w := (10939 / 36539)) (n := 12)
    (lo := (308837047 / 500000000)) (hi := (123534819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23739 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23739 / 12800) = 1/(12800 / 23739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (308837047 / 500000000) (123534819 / 200000000) (Real.log (23739 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23739 / 12800) = -Real.log (12800 / 23739) := by
    rw [show ((23739 / 12800) : ℝ) = ((12800 / 23739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (241041399 / 125000000) ≤ -Real.log (1861 / 12800) ∧
    -Real.log (1861 / 12800) ≤ (385666239 / 200000000) := by
  have h := checkLog_sound (w := (1339 / 5061)) (n := 12)
    (lo := (16938651 / 31250000)) (hi := (542036833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1861) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1861) = 1/(1861 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-385666239 / 200000000) (-241041399 / 125000000) (Real.log (1861 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (166000643 / 250000000) ≤ -Real.log (125000 / 242819) ∧
    -Real.log (125000 / 242819) ≤ (664002573 / 1000000000) := by
  have h := checkLog_sound (w := (117819 / 367819)) (n := 12)
    (lo := (166000643 / 250000000)) (hi := (664002573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242819 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242819 / 125000) = 1/(125000 / 242819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (166000643 / 250000000) (664002573 / 1000000000) (Real.log (242819 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (242819 / 125000) = -Real.log (125000 / 242819) := by
    rw [show ((242819 / 125000) : ℝ) = ((125000 / 242819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (571375017 / 200000000) ≤ -Real.log (7181 / 125000) ∧
    -Real.log (7181 / 125000) ≤ (285687509 / 100000000) := by
  have h := checkLog_sound (w := (1263 / 29987)) (n := 12)
    (lo := (16857273 / 200000000)) (hi := (42143183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14362) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 14362) = 1/(7181 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-285687509 / 100000000) (-571375017 / 200000000) (Real.log (7181 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (664279489 / 1000000000) ≤ -Real.log (100000 / 194309) ∧
    -Real.log (100000 / 194309) ≤ (66427949 / 100000000) := by
  have h := checkLog_sound (w := (94309 / 294309)) (n := 12)
    (lo := (664279489 / 1000000000)) (hi := (66427949 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194309 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194309 / 100000) = 1/(100000 / 194309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (664279489 / 1000000000) (66427949 / 100000000) (Real.log (194309 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (194309 / 100000) = -Real.log (100000 / 194309) := by
    rw [show ((194309 / 100000) : ℝ) = ((100000 / 194309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (716571051 / 250000000) ≤ -Real.log (5691 / 100000) ∧
    -Real.log (5691 / 100000) ≤ (2866284209 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 11941)) (n := 12)
    (lo := (23423871 / 250000000)) (hi := (18739097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5691) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 5691) = 1/(5691 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2866284209 / 1000000000) (-716571051 / 250000000) (Real.log (5691 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (331710347 / 500000000) ≤ -Real.log (500000 / 970711) ∧
    -Real.log (500000 / 970711) ≤ (132684139 / 200000000) := by
  have h := checkLog_sound (w := (470711 / 1470711)) (n := 12)
    (lo := (331710347 / 500000000)) (hi := (132684139 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970711 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970711 / 500000) = 1/(500000 / 970711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (331710347 / 500000000) (132684139 / 200000000) (Real.log (970711 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (970711 / 500000) = -Real.log (500000 / 970711) := by
    rw [show ((970711 / 500000) : ℝ) = ((500000 / 970711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2837396077 / 1000000000) ≤ -Real.log (29289 / 500000) ∧
    -Real.log (29289 / 500000) ≤ (1418698041 / 500000000) := by
  have h := checkLog_sound (w := (1961 / 60539)) (n := 12)
    (lo := (64807357 / 1000000000)) (hi := (32403679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29289) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 29289) = 1/(29289 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1418698041 / 500000000) (-2837396077 / 1000000000) (Real.log (29289 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (16592779 / 25000000) ≤ -Real.log (500000 / 970993) ∧
    -Real.log (500000 / 970993) ≤ (663711161 / 1000000000) := by
  have h := checkLog_sound (w := (470993 / 1470993)) (n := 12)
    (lo := (16592779 / 25000000)) (hi := (663711161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970993 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970993 / 500000) = 1/(500000 / 970993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (16592779 / 25000000) (663711161 / 1000000000) (Real.log (970993 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (970993 / 500000) = -Real.log (500000 / 970993) := by
    rw [show ((970993 / 500000) : ℝ) = ((500000 / 970993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (711767729 / 250000000) ≤ -Real.log (29007 / 500000) ∧
    -Real.log (29007 / 500000) ≤ (2847070921 / 1000000000) := by
  have h := checkLog_sound (w := (2243 / 60257)) (n := 12)
    (lo := (18620549 / 250000000)) (hi := (74482197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29007) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 29007) = 1/(29007 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2847070921 / 1000000000) (-711767729 / 250000000) (Real.log (29007 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3520877657 / 1000000000) ≤ -Real.log (500000000000 / 16907046372371) ∧
    -Real.log (500000000000 / 16907046372371) ≤ (3520877663 / 1000000000) := by
  have h := checkLog_sound (w := (907046372371 / 32907046372371)) (n := 12)
    (lo := (55141757 / 1000000000)) (hi := (27570879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16907046372371 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16907046372371 / 16000000000000) = 1/(500000000000 / 16907046372371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3520877657 / 1000000000) (3520877663 / 1000000000) (Real.log (16907046372371 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (16907046372371 / 500000000000) = -Real.log (500000000000 / 16907046372371) := by
    rw [show ((16907046372371 / 500000000000) : ℝ) = ((500000000000 / 16907046372371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3530563693 / 1000000000) ≤ -Real.log (31250000000 / 1066975267967) ∧
    -Real.log (31250000000 / 1066975267967) ≤ (3530563699 / 1000000000) := by
  have h := checkLog_sound (w := (66975267967 / 2066975267967)) (n := 12)
    (lo := (64827793 / 1000000000)) (hi := (32413897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1066975267967 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1066975267967 / 1000000000000) = 1/(31250000000 / 1066975267967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3530563693 / 1000000000) (3530563699 / 1000000000) (Real.log (1066975267967 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1066975267967 / 31250000000) = -Real.log (31250000000 / 1066975267967) := by
    rw [show ((1066975267967 / 31250000000) : ℝ) = ((31250000000 / 1066975267967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (350081677 / 100000000) ≤ -Real.log (500000000000 / 16571255420123) ∧
    -Real.log (500000000000 / 16571255420123) ≤ (437602097 / 125000000) := by
  have h := checkLog_sound (w := (571255420123 / 32571255420123)) (n := 12)
    (lo := (3508087 / 100000000)) (hi := (35080871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16571255420123 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16571255420123 / 16000000000000) = 1/(500000000000 / 16571255420123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (350081677 / 100000000) (437602097 / 125000000) (Real.log (16571255420123 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (16571255420123 / 500000000000) = -Real.log (500000000000 / 16571255420123) := by
    rw [show ((16571255420123 / 500000000000) : ℝ) = ((500000000000 / 16571255420123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (877695519 / 250000000) ≤ -Real.log (500000000000 / 16737218602407) ∧
    -Real.log (500000000000 / 16737218602407) ≤ (1755391041 / 500000000) := by
  have h := checkLog_sound (w := (737218602407 / 32737218602407)) (n := 12)
    (lo := (1407693 / 31250000)) (hi := (45046177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16737218602407 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16737218602407 / 16000000000000) = 1/(500000000000 / 16737218602407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (877695519 / 250000000) (1755391041 / 500000000) (Real.log (16737218602407 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16737218602407 / 500000000000) = -Real.log (500000000000 / 16737218602407) := by
    rw [show ((16737218602407 / 500000000000) : ℝ) = ((500000000000 / 16737218602407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0145

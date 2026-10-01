import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0137
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

theorem reflection_log_1_neg : (659582317 / 1000000000) ≤ -Real.log (2560 / 4951) ∧
    -Real.log (2560 / 4951) ≤ (329791159 / 500000000) := by
  have h := checkLog_sound (w := (2391 / 7511)) (n := 12)
    (lo := (659582317 / 1000000000)) (hi := (329791159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4951 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4951 / 2560) = 1/(2560 / 4951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (659582317 / 1000000000) (329791159 / 500000000) (Real.log (4951 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4951 / 2560) = -Real.log (2560 / 4951) := by
    rw [show ((4951 / 2560) : ℝ) = ((2560 / 4951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (135893191 / 50000000) ≤ -Real.log (169 / 2560) ∧
    -Real.log (169 / 2560) ≤ (169866489 / 62500000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 169) = 1/(169 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-169866489 / 62500000) (-135893191 / 50000000) (Real.log (169 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (659198483 / 1000000000) ≤ -Real.log (25600 / 49491) ∧
    -Real.log (25600 / 49491) ≤ (164799621 / 250000000) := by
  have h := checkLog_sound (w := (23891 / 75091)) (n := 12)
    (lo := (659198483 / 1000000000)) (hi := (164799621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49491 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49491 / 25600) = 1/(25600 / 49491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (659198483 / 1000000000) (164799621 / 250000000) (Real.log (49491 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49491 / 25600) = -Real.log (25600 / 49491) := by
    rw [show ((49491 / 25600) : ℝ) = ((25600 / 49491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (541336789 / 200000000) ≤ -Real.log (1709 / 25600) ∧
    -Real.log (1709 / 25600) ≤ (2706683949 / 1000000000) := by
  have h := checkLog_sound (w := (1491 / 4909)) (n := 12)
    (lo := (125448481 / 200000000)) (hi := (313621203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1709) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1709) = 1/(1709 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2706683949 / 1000000000) (-541336789 / 200000000) (Real.log (1709 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (62485161 / 100000000) ≤ -Real.log (1280 / 2391) ∧
    -Real.log (1280 / 2391) ≤ (624851611 / 1000000000) := by
  have h := checkLog_sound (w := (1111 / 3671)) (n := 12)
    (lo := (62485161 / 100000000)) (hi := (624851611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2391 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2391 / 1280) = 1/(1280 / 2391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (62485161 / 100000000) (624851611 / 1000000000) (Real.log (2391 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2391 / 1280) = -Real.log (1280 / 2391) := by
    rw [show ((2391 / 1280) : ℝ) = ((1280 / 2391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12654479 / 6250000) ≤ -Real.log (169 / 1280) ∧
    -Real.log (169 / 1280) ≤ (2024716643 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 169) = 1/(169 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2024716643 / 1000000000) (-12654479 / 6250000) (Real.log (169 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (78007081 / 125000000) ≤ -Real.log (12800 / 23891) ∧
    -Real.log (12800 / 23891) ≤ (624056649 / 1000000000) := by
  have h := checkLog_sound (w := (11091 / 36691)) (n := 12)
    (lo := (78007081 / 125000000)) (hi := (624056649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23891 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23891 / 12800) = 1/(12800 / 23891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (78007081 / 125000000) (624056649 / 1000000000) (Real.log (23891 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23891 / 12800) = -Real.log (12800 / 23891) := by
    rw [show ((23891 / 12800) : ℝ) = ((12800 / 23891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (402707353 / 200000000) ≤ -Real.log (1709 / 12800) ∧
    -Real.log (1709 / 12800) ≤ (3932689 / 1953125) := by
  have h := checkLog_sound (w := (1491 / 4909)) (n := 12)
    (lo := (125448481 / 200000000)) (hi := (313621203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1709) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1709) = 1/(1709 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3932689 / 1953125) (-402707353 / 200000000) (Real.log (1709 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (133244899 / 200000000) ≤ -Real.log (1000000 / 1946873) ∧
    -Real.log (1000000 / 1946873) ≤ (41639031 / 62500000) := by
  have h := checkLog_sound (w := (946873 / 2946873)) (n := 12)
    (lo := (133244899 / 200000000)) (hi := (41639031 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1946873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1946873 / 1000000) = 1/(1000000 / 1946873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (133244899 / 200000000) (41639031 / 62500000) (Real.log (1946873 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1946873 / 1000000) = -Real.log (1000000 / 1946873) := by
    rw [show ((1946873 / 1000000) : ℝ) = ((1000000 / 1946873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2935070003 / 1000000000) ≤ -Real.log (53127 / 1000000) ∧
    -Real.log (53127 / 1000000) ≤ (366883751 / 125000000) := by
  have h := checkLog_sound (w := (9373 / 115627)) (n := 12)
    (lo := (162481283 / 1000000000)) (hi := (40620321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53127) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 53127) = 1/(53127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-366883751 / 125000000) (-2935070003 / 1000000000) (Real.log (53127 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83313049 / 125000000) ≤ -Real.log (500000 / 973709) ∧
    -Real.log (500000 / 973709) ≤ (666504393 / 1000000000) := by
  have h := checkLog_sound (w := (473709 / 1473709)) (n := 12)
    (lo := (83313049 / 125000000)) (hi := (666504393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973709 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973709 / 500000) = 1/(500000 / 973709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83313049 / 125000000) (666504393 / 1000000000) (Real.log (973709 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (973709 / 500000) = -Real.log (500000 / 973709) := by
    rw [show ((973709 / 500000) : ℝ) = ((500000 / 973709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (147269071 / 50000000) ≤ -Real.log (26291 / 500000) ∧
    -Real.log (26291 / 500000) ≤ (117815257 / 40000000) := by
  have h := checkLog_sound (w := (4959 / 57541)) (n := 12)
    (lo := (1727927 / 10000000)) (hi := (172792701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26291) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 26291) = 1/(26291 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-117815257 / 40000000) (-147269071 / 50000000) (Real.log (26291 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (332873603 / 500000000) ≤ -Real.log (125000 / 243243) ∧
    -Real.log (125000 / 243243) ≤ (665747207 / 1000000000) := by
  have h := checkLog_sound (w := (118243 / 368243)) (n := 12)
    (lo := (332873603 / 500000000)) (hi := (665747207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243243 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243243 / 125000) = 1/(125000 / 243243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (332873603 / 500000000) (665747207 / 1000000000) (Real.log (243243 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (243243 / 125000) = -Real.log (125000 / 243243) := by
    rw [show ((243243 / 125000) : ℝ) = ((125000 / 243243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (291773473 / 100000000) ≤ -Real.log (6757 / 125000) ∧
    -Real.log (6757 / 125000) ≤ (583546947 / 200000000) := by
  have h := checkLog_sound (w := (2111 / 29139)) (n := 12)
    (lo := (14514601 / 100000000)) (hi := (145146011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13514) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 13514) = 1/(6757 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-583546947 / 200000000) (-291773473 / 100000000) (Real.log (6757 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (166509763 / 250000000) ≤ -Real.log (62500 / 121657) ∧
    -Real.log (62500 / 121657) ≤ (666039053 / 1000000000) := by
  have h := checkLog_sound (w := (59157 / 184157)) (n := 12)
    (lo := (166509763 / 250000000)) (hi := (666039053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121657 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121657 / 62500) = 1/(62500 / 121657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (166509763 / 250000000) (666039053 / 1000000000) (Real.log (121657 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (121657 / 62500) = -Real.log (62500 / 121657) := by
    rw [show ((121657 / 62500) : ℝ) = ((62500 / 121657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2928297947 / 1000000000) ≤ -Real.log (3343 / 62500) ∧
    -Real.log (3343 / 62500) ≤ (91509311 / 31250000) := by
  have h := checkLog_sound (w := (2253 / 28997)) (n := 12)
    (lo := (155709227 / 1000000000)) (hi := (38927307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13372) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 13372) = 1/(3343 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-91509311 / 31250000) (-2928297947 / 1000000000) (Real.log (3343 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1800647249 / 500000000) ≤ -Real.log (500000000000 / 18322820787923) ∧
    -Real.log (500000000000 / 18322820787923) ≤ (450161813 / 125000000) := by
  have h := checkLog_sound (w := (2322820787923 / 34322820787923)) (n := 12)
    (lo := (67779299 / 500000000)) (hi := (135558599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18322820787923 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18322820787923 / 16000000000000) = 1/(500000000000 / 18322820787923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1800647249 / 500000000) (450161813 / 125000000) (Real.log (18322820787923 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (18322820787923 / 500000000000) = -Real.log (500000000000 / 18322820787923) := by
    rw [show ((18322820787923 / 500000000000) : ℝ) = ((500000000000 / 18322820787923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (902971453 / 250000000) ≤ -Real.log (250000000000 / 9258957437907) ∧
    -Real.log (250000000000 / 9258957437907) ≤ (1805942909 / 500000000) := by
  have h := checkLog_sound (w := (1258957437907 / 17258957437907)) (n := 12)
    (lo := (18268739 / 125000000)) (hi := (146149913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9258957437907 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9258957437907 / 8000000000000) = 1/(250000000000 / 9258957437907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (902971453 / 250000000) (1805942909 / 500000000) (Real.log (9258957437907 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9258957437907 / 250000000000) = -Real.log (250000000000 / 9258957437907) := by
    rw [show ((9258957437907 / 250000000000) : ℝ) = ((250000000000 / 9258957437907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (223967621 / 62500000) ≤ -Real.log (20000000000 / 719973360959) ∧
    -Real.log (20000000000 / 719973360959) ≤ (1791740971 / 500000000) := by
  have h := checkLog_sound (w := (79973360959 / 1359973360959)) (n := 12)
    (lo := (29436509 / 250000000)) (hi := (117746037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719973360959 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(719973360959 / 640000000000) = 1/(20000000000 / 719973360959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (223967621 / 62500000) (1791740971 / 500000000) (Real.log (719973360959 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (719973360959 / 20000000000) = -Real.log (20000000000 / 719973360959) := by
    rw [show ((719973360959 / 20000000000) : ℝ) = ((20000000000 / 719973360959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3594336999 / 1000000000) ≤ -Real.log (500000000000 / 18195782231529) ∧
    -Real.log (500000000000 / 18195782231529) ≤ (718867401 / 200000000) := by
  have h := checkLog_sound (w := (2195782231529 / 34195782231529)) (n := 12)
    (lo := (128601099 / 1000000000)) (hi := (1286011 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18195782231529 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18195782231529 / 16000000000000) = 1/(500000000000 / 18195782231529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3594336999 / 1000000000) (718867401 / 200000000) (Real.log (18195782231529 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (18195782231529 / 500000000000) = -Real.log (500000000000 / 18195782231529) := by
    rw [show ((18195782231529 / 500000000000) : ℝ) = ((500000000000 / 18195782231529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0137

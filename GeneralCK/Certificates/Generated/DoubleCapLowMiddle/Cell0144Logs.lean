import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0144
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

theorem reflection_log_1_neg : (656892377 / 1000000000) ≤ -Real.log (25600 / 49377) ∧
    -Real.log (25600 / 49377) ≤ (328446189 / 500000000) := by
  have h := checkLog_sound (w := (23777 / 74977)) (n := 12)
    (lo := (656892377 / 1000000000)) (hi := (328446189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49377 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49377 / 25600) = 1/(25600 / 49377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (656892377 / 1000000000) (328446189 / 500000000) (Real.log (49377 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49377 / 25600) = -Real.log (25600 / 49377) := by
    rw [show ((49377 / 25600) : ℝ) = ((25600 / 49377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1321054427 / 500000000) ≤ -Real.log (1823 / 25600) ∧
    -Real.log (1823 / 25600) ≤ (1321054429 / 500000000) := by
  have h := checkLog_sound (w := (1377 / 5023)) (n := 12)
    (lo := (281333657 / 500000000)) (hi := (112533463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1823) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1823) = 1/(1823 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1321054429 / 500000000) (-1321054427 / 500000000) (Real.log (1823 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (164126877 / 250000000) ≤ -Real.log (12800 / 24679) ∧
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


theorem reflection_log_3 : Bounds (164126877 / 250000000) (656507509 / 1000000000) (Real.log (24679 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24679 / 12800) = -Real.log (12800 / 24679) := by
    rw [show ((24679 / 12800) : ℝ) = ((12800 / 24679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2631740411 / 1000000000) ≤ -Real.log (921 / 12800) ∧
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


theorem reflection_log_4 : Bounds (-526348083 / 200000000) (-2631740411 / 1000000000) (Real.log (921 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (123854711 / 200000000) ≤ -Real.log (12800 / 23777) ∧
    -Real.log (12800 / 23777) ≤ (154818389 / 250000000) := by
  have h := checkLog_sound (w := (10977 / 36577)) (n := 12)
    (lo := (123854711 / 200000000)) (hi := (154818389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23777 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23777 / 12800) = 1/(12800 / 23777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (123854711 / 200000000) (154818389 / 250000000) (Real.log (23777 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23777 / 12800) = -Real.log (12800 / 23777) := by
    rw [show ((23777 / 12800) : ℝ) = ((12800 / 23777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (974480837 / 500000000) ≤ -Real.log (1823 / 12800) ∧
    -Real.log (1823 / 12800) ≤ (1948961677 / 1000000000) := by
  have h := checkLog_sound (w := (1377 / 5023)) (n := 12)
    (lo := (281333657 / 500000000)) (hi := (112533463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1823) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1823) = 1/(1823 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1948961677 / 1000000000) (-974480837 / 500000000) (Real.log (1823 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (19327317 / 31250000) ≤ -Real.log (6400 / 11879) ∧
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


theorem reflection_log_7 : Bounds (19327317 / 31250000) (123694829 / 200000000) (Real.log (11879 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11879 / 6400) = -Real.log (6400 / 11879) := by
    rw [show ((11879 / 6400) : ℝ) = ((6400 / 11879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1938593231 / 1000000000) ≤ -Real.log (921 / 6400) ∧
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


theorem reflection_log_8 : Bounds (-969296617 / 500000000) (-1938593231 / 1000000000) (Real.log (921 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (332139487 / 500000000) ≤ -Real.log (1000000 / 1943089) ∧
    -Real.log (1000000 / 1943089) ≤ (26571159 / 40000000) := by
  have h := checkLog_sound (w := (943089 / 2943089)) (n := 12)
    (lo := (332139487 / 500000000)) (hi := (26571159 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1943089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1943089 / 1000000) = 1/(1000000 / 1943089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (332139487 / 500000000) (26571159 / 40000000) (Real.log (1943089 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1943089 / 1000000) = -Real.log (1000000 / 1943089) := by
    rw [show ((1943089 / 1000000) : ℝ) = ((1000000 / 1943089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (358283329 / 125000000) ≤ -Real.log (56911 / 1000000) ∧
    -Real.log (56911 / 1000000) ≤ (2866266637 / 1000000000) := by
  have h := checkLog_sound (w := (5589 / 119411)) (n := 12)
    (lo := (11709739 / 125000000)) (hi := (93677913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56911) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 56911) = 1/(56911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2866266637 / 1000000000) (-358283329 / 125000000) (Real.log (56911 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (664556329 / 1000000000) ≤ -Real.log (250000 / 485907) ∧
    -Real.log (250000 / 485907) ≤ (66455633 / 100000000) := by
  have h := checkLog_sound (w := (235907 / 735907)) (n := 12)
    (lo := (664556329 / 1000000000)) (hi := (66455633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((485907 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(485907 / 250000) = 1/(250000 / 485907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (664556329 / 1000000000) (66455633 / 100000000) (Real.log (485907 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (485907 / 250000) = -Real.log (250000 / 485907) := by
    rw [show ((485907 / 250000) : ℝ) = ((250000 / 485907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (575156539 / 200000000) ≤ -Real.log (14093 / 250000) ∧
    -Real.log (14093 / 250000) ≤ (28757827 / 10000000) := by
  have h := checkLog_sound (w := (766 / 14859)) (n := 12)
    (lo := (4127759 / 40000000)) (hi := (12899247 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14093) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 14093) = 1/(14093 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-28757827 / 10000000) (-575156539 / 200000000) (Real.log (14093 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (132742129 / 200000000) ≤ -Real.log (200000 / 388397) ∧
    -Real.log (200000 / 388397) ≤ (331855323 / 500000000) := by
  have h := checkLog_sound (w := (188397 / 588397)) (n := 12)
    (lo := (132742129 / 200000000)) (hi := (331855323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388397 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388397 / 200000) = 1/(200000 / 388397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (132742129 / 200000000) (331855323 / 500000000) (Real.log (388397 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (388397 / 200000) = -Real.log (200000 / 388397) := by
    rw [show ((388397 / 200000) : ℝ) = ((200000 / 388397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1423526839 / 500000000) ≤ -Real.log (11603 / 200000) ∧
    -Real.log (11603 / 200000) ≤ (2847053683 / 1000000000) := by
  have h := checkLog_sound (w := (897 / 24103)) (n := 12)
    (lo := (37232479 / 500000000)) (hi := (74464959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11603) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 11603) = 1/(11603 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2847053683 / 1000000000) (-1423526839 / 500000000) (Real.log (11603 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (332000771 / 500000000) ≤ -Real.log (20000 / 38851) ∧
    -Real.log (20000 / 38851) ≤ (664001543 / 1000000000) := by
  have h := checkLog_sound (w := (18851 / 58851)) (n := 12)
    (lo := (332000771 / 500000000)) (hi := (664001543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38851 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38851 / 20000) = 1/(20000 / 38851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (332000771 / 500000000) (664001543 / 1000000000) (Real.log (38851 / 20000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (38851 / 20000) = -Real.log (20000 / 38851) := by
    rw [show ((38851 / 20000) : ℝ) = ((20000 / 38851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (178552517 / 62500000) ≤ -Real.log (1149 / 20000) ∧
    -Real.log (1149 / 20000) ≤ (2856840277 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 2399)) (n := 12)
    (lo := (2632861 / 31250000)) (hi := (84251553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1149) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1250 / 1149) = 1/(1149 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2856840277 / 1000000000) (-178552517 / 62500000) (Real.log (1149 / 20000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1765272803 / 500000000) ≤ -Real.log (500000000000 / 17071295531619) ∧
    -Real.log (500000000000 / 17071295531619) ≤ (882636403 / 250000000) := by
  have h := checkLog_sound (w := (1071295531619 / 33071295531619)) (n := 12)
    (lo := (32404853 / 500000000)) (hi := (64809707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17071295531619 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17071295531619 / 16000000000000) = 1/(500000000000 / 17071295531619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1765272803 / 500000000) (882636403 / 250000000) (Real.log (17071295531619 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (17071295531619 / 500000000000) = -Real.log (500000000000 / 17071295531619) := by
    rw [show ((17071295531619 / 500000000000) : ℝ) = ((500000000000 / 17071295531619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (221271189 / 62500000) ≤ -Real.log (500000000000 / 17239303200171) ∧
    -Real.log (500000000000 / 17239303200171) ≤ (354033903 / 100000000) := by
  have h := checkLog_sound (w := (1239303200171 / 33239303200171)) (n := 12)
    (lo := (18650781 / 250000000)) (hi := (23873 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17239303200171 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17239303200171 / 16000000000000) = 1/(500000000000 / 17239303200171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (221271189 / 62500000) (354033903 / 100000000) (Real.log (17239303200171 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (17239303200171 / 500000000000) = -Real.log (500000000000 / 17239303200171) := by
    rw [show ((17239303200171 / 500000000000) : ℝ) = ((500000000000 / 17239303200171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (877691081 / 250000000) ≤ -Real.log (250000000000 / 8368460742911) ∧
    -Real.log (250000000000 / 8368460742911) ≤ (351076433 / 100000000) := by
  have h := checkLog_sound (w := (368460742911 / 16368460742911)) (n := 12)
    (lo := (5628553 / 125000000)) (hi := (1801137 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8368460742911 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8368460742911 / 8000000000000) = 1/(250000000000 / 8368460742911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (877691081 / 250000000) (351076433 / 100000000) (Real.log (8368460742911 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8368460742911 / 250000000000) = -Real.log (250000000000 / 8368460742911) := by
    rw [show ((8368460742911 / 250000000000) : ℝ) = ((250000000000 / 8368460742911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1760420907 / 500000000) ≤ -Real.log (250000000000 / 8453220191471) ∧
    -Real.log (250000000000 / 8453220191471) ≤ (176042091 / 50000000) := by
  have h := checkLog_sound (w := (453220191471 / 16453220191471)) (n := 12)
    (lo := (27552957 / 500000000)) (hi := (11021183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8453220191471 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8453220191471 / 8000000000000) = 1/(250000000000 / 8453220191471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1760420907 / 500000000) (176042091 / 50000000) (Real.log (8453220191471 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8453220191471 / 250000000000) = -Real.log (250000000000 / 8453220191471) := by
    rw [show ((8453220191471 / 250000000000) : ℝ) = ((250000000000 / 8453220191471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0144

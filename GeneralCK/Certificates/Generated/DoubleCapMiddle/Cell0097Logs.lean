import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0097
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

theorem reflection_log_1_neg : (67182809 / 200000000) ≤ -Real.log (1280 / 1791) ∧
    -Real.log (1280 / 1791) ≤ (167957023 / 500000000) := by
  have h := checkLog_sound (w := (511 / 3071)) (n := 12)
    (lo := (67182809 / 200000000)) (hi := (167957023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1791 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1791 / 1280) = 1/(1280 / 1791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67182809 / 200000000) (167957023 / 500000000) (Real.log (1791 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1791 / 1280) = -Real.log (1280 / 1791) := by
    rw [show ((1791 / 1280) : ℝ) = ((1280 / 1791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (509524387 / 1000000000) ≤ -Real.log (769 / 1280) ∧
    -Real.log (769 / 1280) ≤ (127381097 / 250000000) := by
  have h := checkLog_sound (w := (511 / 2049)) (n := 12)
    (lo := (509524387 / 1000000000)) (hi := (127381097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 769) = 1/(769 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-127381097 / 250000000) (-509524387 / 1000000000) (Real.log (769 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (335076173 / 1000000000) ≤ -Real.log (2560 / 3579) ∧
    -Real.log (2560 / 3579) ≤ (167538087 / 500000000) := by
  have h := checkLog_sound (w := (1019 / 6139)) (n := 12)
    (lo := (335076173 / 1000000000)) (hi := (167538087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3579 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3579 / 2560) = 1/(2560 / 3579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (335076173 / 1000000000) (167538087 / 500000000) (Real.log (3579 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3579 / 2560) = -Real.log (2560 / 3579) := by
    rw [show ((3579 / 2560) : ℝ) = ((2560 / 3579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (253787851 / 500000000) ≤ -Real.log (1541 / 2560) ∧
    -Real.log (1541 / 2560) ≤ (507575703 / 1000000000) := by
  have h := checkLog_sound (w := (1019 / 4101)) (n := 12)
    (lo := (253787851 / 500000000)) (hi := (507575703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1541) = 1/(1541 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-507575703 / 1000000000) (-253787851 / 500000000) (Real.log (1541 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (73364779 / 125000000) ≤ -Real.log (640 / 1151) ∧
    -Real.log (640 / 1151) ≤ (586918233 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 1791)) (n := 12)
    (lo := (73364779 / 125000000)) (hi := (586918233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151 / 640) = 1/(640 / 1151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (73364779 / 125000000) (586918233 / 1000000000) (Real.log (1151 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1151 / 640) = -Real.log (640 / 1151) := by
    rw [show ((1151 / 640) : ℝ) = ((640 / 1151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (160165577 / 100000000) ≤ -Real.log (129 / 640) ∧
    -Real.log (129 / 640) ≤ (1601655773 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 129) = 1/(129 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1601655773 / 1000000000) (-160165577 / 100000000) (Real.log (129 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (585614167 / 1000000000) ≤ -Real.log (1280 / 2299) ∧
    -Real.log (1280 / 2299) ≤ (73201771 / 125000000) := by
  have h := checkLog_sound (w := (1019 / 3579)) (n := 12)
    (lo := (585614167 / 1000000000)) (hi := (73201771 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2299 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2299 / 1280) = 1/(1280 / 2299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (585614167 / 1000000000) (73201771 / 125000000) (Real.log (2299 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2299 / 1280) = -Real.log (1280 / 2299) := by
    rw [show ((2299 / 1280) : ℝ) = ((1280 / 2299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (397523737 / 250000000) ≤ -Real.log (261 / 1280) ∧
    -Real.log (261 / 1280) ≤ (1590094951 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 581)) (n := 12)
    (lo := (50950147 / 250000000)) (hi := (203800589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 261) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 261) = 1/(261 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1590094951 / 1000000000) (-397523737 / 250000000) (Real.log (261 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (459994959 / 1000000000) ≤ -Real.log (500000 / 792033) ∧
    -Real.log (500000 / 792033) ≤ (5749937 / 12500000) := by
  have h := checkLog_sound (w := (292033 / 1292033)) (n := 12)
    (lo := (459994959 / 1000000000)) (hi := (5749937 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792033 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792033 / 500000) = 1/(500000 / 792033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (459994959 / 1000000000) (5749937 / 12500000) (Real.log (792033 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (792033 / 500000) = -Real.log (500000 / 792033) := by
    rw [show ((792033 / 500000) : ℝ) = ((500000 / 792033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (219307171 / 250000000) ≤ -Real.log (207967 / 500000) ∧
    -Real.log (207967 / 500000) ≤ (438614343 / 500000000) := by
  have h := checkLog_sound (w := (42033 / 457967)) (n := 12)
    (lo := (5752547 / 31250000)) (hi := (36816301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207967) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 207967) = 1/(207967 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-438614343 / 500000000) (-219307171 / 250000000) (Real.log (207967 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (180156 / 390625) ≤ -Real.log (40000 / 63439) ∧
    -Real.log (40000 / 63439) ≤ (461199361 / 1000000000) := by
  have h := checkLog_sound (w := (23439 / 103439)) (n := 12)
    (lo := (180156 / 390625)) (hi := (461199361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63439 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63439 / 40000) = 1/(40000 / 63439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (180156 / 390625) (461199361 / 1000000000) (Real.log (63439 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (63439 / 40000) = -Real.log (40000 / 63439) := by
    rw [show ((63439 / 40000) : ℝ) = ((40000 / 63439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (881828919 / 1000000000) ≤ -Real.log (16561 / 40000) ∧
    -Real.log (16561 / 40000) ≤ (881828921 / 1000000000) := by
  have h := checkLog_sound (w := (3439 / 36561)) (n := 12)
    (lo := (188681739 / 1000000000)) (hi := (9434087 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16561) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 16561) = 1/(16561 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-881828921 / 1000000000) (-881828919 / 1000000000) (Real.log (16561 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (375519857 / 1000000000) ≤ -Real.log (250000 / 363937) ∧
    -Real.log (250000 / 363937) ≤ (187759929 / 500000000) := by
  have h := checkLog_sound (w := (113937 / 613937)) (n := 12)
    (lo := (375519857 / 1000000000)) (hi := (187759929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363937 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363937 / 250000) = 1/(250000 / 363937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (375519857 / 1000000000) (187759929 / 500000000) (Real.log (363937 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (363937 / 250000) = -Real.log (250000 / 363937) := by
    rw [show ((363937 / 250000) : ℝ) = ((250000 / 363937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (76042863 / 125000000) ≤ -Real.log (136063 / 250000) ∧
    -Real.log (136063 / 250000) ≤ (121668581 / 200000000) := by
  have h := checkLog_sound (w := (113937 / 386063)) (n := 12)
    (lo := (76042863 / 125000000)) (hi := (121668581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 136063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 136063) = 1/(136063 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-121668581 / 200000000) (-76042863 / 125000000) (Real.log (136063 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (376752827 / 1000000000) ≤ -Real.log (125000 / 182193) ∧
    -Real.log (125000 / 182193) ≤ (94188207 / 250000000) := by
  have h := checkLog_sound (w := (57193 / 307193)) (n := 12)
    (lo := (376752827 / 1000000000)) (hi := (94188207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182193 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182193 / 125000) = 1/(125000 / 182193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (376752827 / 1000000000) (94188207 / 250000000) (Real.log (182193 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (182193 / 125000) = -Real.log (125000 / 182193) := by
    rw [show ((182193 / 125000) : ℝ) = ((125000 / 182193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (305824151 / 500000000) ≤ -Real.log (67807 / 125000) ∧
    -Real.log (67807 / 125000) ≤ (611648303 / 1000000000) := by
  have h := checkLog_sound (w := (57193 / 192807)) (n := 12)
    (lo := (305824151 / 500000000)) (hi := (611648303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 67807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 67807) = 1/(67807 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-611648303 / 1000000000) (-305824151 / 500000000) (Real.log (67807 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1337223643 / 1000000000) ≤ -Real.log (2500000000 / 9521137969) ∧
    -Real.log (2500000000 / 9521137969) ≤ (267444729 / 200000000) := by
  have h := checkLog_sound (w := (4521137969 / 14521137969)) (n := 12)
    (lo := (644076463 / 1000000000)) (hi := (40254779 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9521137969 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9521137969 / 5000000000) = 1/(2500000000 / 9521137969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1337223643 / 1000000000) (267444729 / 200000000) (Real.log (9521137969 / 2500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9521137969 / 2500000000) = -Real.log (2500000000 / 9521137969) := by
    rw [show ((9521137969 / 2500000000) : ℝ) = ((2500000000 / 9521137969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (33575707 / 25000000) ≤ -Real.log (500000000000 / 1915313084959) ∧
    -Real.log (500000000000 / 1915313084959) ≤ (671514141 / 500000000) := by
  have h := checkLog_sound (w := (915313084959 / 2915313084959)) (n := 12)
    (lo := (6498811 / 10000000)) (hi := (649881101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1915313084959 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1915313084959 / 1000000000000) = 1/(500000000000 / 1915313084959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (33575707 / 25000000) (671514141 / 500000000) (Real.log (1915313084959 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1915313084959 / 500000000000) = -Real.log (500000000000 / 1915313084959) := by
    rw [show ((1915313084959 / 500000000000) : ℝ) = ((500000000000 / 1915313084959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (983862761 / 1000000000) ≤ -Real.log (500000000000 / 1337384152929) ∧
    -Real.log (500000000000 / 1337384152929) ≤ (983862763 / 1000000000) := by
  have h := checkLog_sound (w := (337384152929 / 2337384152929)) (n := 12)
    (lo := (290715581 / 1000000000)) (hi := (145357791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337384152929 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1337384152929 / 1000000000000) = 1/(500000000000 / 1337384152929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (983862761 / 1000000000) (983862763 / 1000000000) (Real.log (1337384152929 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1337384152929 / 500000000000) = -Real.log (500000000000 / 1337384152929) := by
    rw [show ((1337384152929 / 500000000000) : ℝ) = ((500000000000 / 1337384152929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (988401129 / 1000000000) ≤ -Real.log (15625000000 / 41983359019) ∧
    -Real.log (15625000000 / 41983359019) ≤ (988401131 / 1000000000) := by
  have h := checkLog_sound (w := (10733359019 / 73233359019)) (n := 12)
    (lo := (295253949 / 1000000000)) (hi := (5905079 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41983359019 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(41983359019 / 31250000000) = 1/(15625000000 / 41983359019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (988401129 / 1000000000) (988401131 / 1000000000) (Real.log (41983359019 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (41983359019 / 15625000000) = -Real.log (15625000000 / 41983359019) := by
    rw [show ((41983359019 / 15625000000) : ℝ) = ((15625000000 / 41983359019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0097

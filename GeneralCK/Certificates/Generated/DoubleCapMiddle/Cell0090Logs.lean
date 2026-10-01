import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0090
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

theorem reflection_log_1_neg : (341759573 / 1000000000) ≤ -Real.log (2560 / 3603) ∧
    -Real.log (2560 / 3603) ≤ (170879787 / 500000000) := by
  have h := checkLog_sound (w := (1043 / 6163)) (n := 12)
    (lo := (341759573 / 1000000000)) (hi := (170879787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3603 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3603 / 2560) = 1/(2560 / 3603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (341759573 / 1000000000) (170879787 / 500000000) (Real.log (3603 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3603 / 2560) = -Real.log (2560 / 3603) := by
    rw [show ((3603 / 2560) : ℝ) = ((2560 / 3603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (261636279 / 500000000) ≤ -Real.log (1517 / 2560) ∧
    -Real.log (1517 / 2560) ≤ (523272559 / 1000000000) := by
  have h := checkLog_sound (w := (1043 / 4077)) (n := 12)
    (lo := (261636279 / 500000000)) (hi := (523272559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1517) = 1/(1517 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-523272559 / 1000000000) (-261636279 / 500000000) (Real.log (1517 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170463293 / 500000000) ≤ -Real.log (32 / 45) ∧
    -Real.log (32 / 45) ≤ (340926587 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 77)) (n := 12)
    (lo := (170463293 / 500000000)) (hi := (340926587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45 / 32) = 1/(32 / 45) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170463293 / 500000000) (340926587 / 1000000000) (Real.log (45 / 32)) := by
  have h := reflection_log_3_neg
  have he : Real.log (45 / 32) = -Real.log (32 / 45) := by
    rw [show ((45 / 32) : ℝ) = ((32 / 45) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (521296923 / 1000000000) ≤ -Real.log (19 / 32) ∧
    -Real.log (19 / 32) ≤ (130324231 / 250000000) := by
  have h := checkLog_sound (w := (13 / 51)) (n := 12)
    (lo := (521296923 / 1000000000)) (hi := (130324231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 19) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 19) = 1/(19 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-130324231 / 250000000) (-521296923 / 1000000000) (Real.log (19 / 32)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (953599 / 1600000) ≤ -Real.log (1280 / 2323) ∧
    -Real.log (1280 / 2323) ≤ (37249961 / 62500000) := by
  have h := checkLog_sound (w := (1043 / 3603)) (n := 12)
    (lo := (953599 / 1600000)) (hi := (37249961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2323 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2323 / 1280) = 1/(1280 / 2323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (953599 / 1600000) (37249961 / 62500000) (Real.log (2323 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2323 / 1280) = -Real.log (1280 / 2323) := by
    rw [show ((2323 / 1280) : ℝ) = ((1280 / 2323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (843277607 / 500000000) ≤ -Real.log (237 / 1280) ∧
    -Real.log (237 / 1280) ≤ (1686555217 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 557)) (n := 12)
    (lo := (150130427 / 500000000)) (hi := (60052171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 237) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 237) = 1/(237 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1686555217 / 1000000000) (-843277607 / 500000000) (Real.log (237 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (594707107 / 1000000000) ≤ -Real.log (16 / 29) ∧
    -Real.log (16 / 29) ≤ (148676777 / 250000000) := by
  have h := checkLog_sound (w := (13 / 45)) (n := 12)
    (lo := (594707107 / 1000000000)) (hi := (148676777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29 / 16) = 1/(16 / 29) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (594707107 / 1000000000) (148676777 / 250000000) (Real.log (29 / 16)) := by
  have h := reflection_log_7_neg
  have he : Real.log (29 / 16) = -Real.log (16 / 29) := by
    rw [show ((29 / 16) : ℝ) = ((16 / 29) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (104623527 / 62500000) ≤ -Real.log (3 / 16) ∧
    -Real.log (3 / 16) ≤ (334795287 / 200000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(4 / 3) = 1/(3 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-334795287 / 200000000) (-104623527 / 62500000) (Real.log (3 / 16)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (93686479 / 200000000) ≤ -Real.log (62500 / 99843) ∧
    -Real.log (62500 / 99843) ≤ (117108099 / 250000000) := by
  have h := checkLog_sound (w := (37343 / 162343)) (n := 12)
    (lo := (93686479 / 200000000)) (hi := (117108099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99843 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99843 / 62500) = 1/(62500 / 99843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (93686479 / 200000000) (117108099 / 250000000) (Real.log (99843 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (99843 / 62500) = -Real.log (62500 / 99843) := by
    rw [show ((99843 / 62500) : ℝ) = ((62500 / 99843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (28438449 / 31250000) ≤ -Real.log (25157 / 62500) ∧
    -Real.log (25157 / 62500) ≤ (91003037 / 100000000) := by
  have h := checkLog_sound (w := (6093 / 56407)) (n := 12)
    (lo := (54220797 / 250000000)) (hi := (216883189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 25157) = 1/(25157 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91003037 / 100000000) (-28438449 / 31250000) (Real.log (25157 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (469641063 / 1000000000) ≤ -Real.log (50000 / 79971) ∧
    -Real.log (50000 / 79971) ≤ (58705133 / 125000000) := by
  have h := checkLog_sound (w := (29971 / 129971)) (n := 12)
    (lo := (469641063 / 1000000000)) (hi := (58705133 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79971 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79971 / 50000) = 1/(50000 / 79971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (469641063 / 1000000000) (58705133 / 125000000) (Real.log (79971 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (79971 / 50000) = -Real.log (50000 / 79971) := by
    rw [show ((79971 / 50000) : ℝ) = ((50000 / 79971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (914841781 / 1000000000) ≤ -Real.log (20029 / 50000) ∧
    -Real.log (20029 / 50000) ≤ (914841783 / 1000000000) := by
  have h := checkLog_sound (w := (4971 / 45029)) (n := 12)
    (lo := (221694601 / 1000000000)) (hi := (110847301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 20029) = 1/(20029 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-914841783 / 1000000000) (-914841781 / 1000000000) (Real.log (20029 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (384204017 / 1000000000) ≤ -Real.log (200000 / 293689) ∧
    -Real.log (200000 / 293689) ≤ (192102009 / 500000000) := by
  have h := checkLog_sound (w := (93689 / 493689)) (n := 12)
    (lo := (384204017 / 1000000000)) (hi := (192102009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293689 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293689 / 200000) = 1/(200000 / 293689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (384204017 / 1000000000) (192102009 / 500000000) (Real.log (293689 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (293689 / 200000) = -Real.log (200000 / 293689) := by
    rw [show ((293689 / 200000) : ℝ) = ((200000 / 293689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (126389721 / 200000000) ≤ -Real.log (106311 / 200000) ∧
    -Real.log (106311 / 200000) ≤ (315974303 / 500000000) := by
  have h := checkLog_sound (w := (93689 / 306311)) (n := 12)
    (lo := (126389721 / 200000000)) (hi := (315974303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 106311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 106311) = 1/(106311 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-315974303 / 500000000) (-126389721 / 200000000) (Real.log (106311 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (385456939 / 1000000000) ≤ -Real.log (500000 / 735143) ∧
    -Real.log (500000 / 735143) ≤ (19272847 / 50000000) := by
  have h := checkLog_sound (w := (235143 / 1235143)) (n := 12)
    (lo := (385456939 / 1000000000)) (hi := (19272847 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735143 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735143 / 500000) = 1/(500000 / 735143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (385456939 / 1000000000) (19272847 / 50000000) (Real.log (735143 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (735143 / 500000) = -Real.log (500000 / 735143) := by
    rw [show ((735143 / 500000) : ℝ) = ((500000 / 735143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (15885451 / 25000000) ≤ -Real.log (264857 / 500000) ∧
    -Real.log (264857 / 500000) ≤ (635418041 / 1000000000) := by
  have h := checkLog_sound (w := (235143 / 764857)) (n := 12)
    (lo := (15885451 / 25000000)) (hi := (635418041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 264857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 264857) = 1/(264857 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-635418041 / 1000000000) (-15885451 / 25000000) (Real.log (264857 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1378462763 / 1000000000) ≤ -Real.log (500000000000 / 1984397980681) ∧
    -Real.log (500000000000 / 1984397980681) ≤ (275692553 / 200000000) := by
  have h := checkLog_sound (w := (984397980681 / 2984397980681)) (n := 12)
    (lo := (685315583 / 1000000000)) (hi := (1338507 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1984397980681 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1984397980681 / 1000000000000) = 1/(500000000000 / 1984397980681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1378462763 / 1000000000) (275692553 / 200000000) (Real.log (1984397980681 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1984397980681 / 500000000000) = -Real.log (500000000000 / 1984397980681) := by
    rw [show ((1984397980681 / 500000000000) : ℝ) = ((500000000000 / 1984397980681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (276896569 / 200000000) ≤ -Real.log (1562500000 / 6238688277) ∧
    -Real.log (1562500000 / 6238688277) ≤ (1384482847 / 1000000000) := by
  have h := checkLog_sound (w := (3113688277 / 9363688277)) (n := 12)
    (lo := (138267133 / 200000000)) (hi := (345667833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6238688277 / 3125000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6238688277 / 3125000000) = 1/(1562500000 / 6238688277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (276896569 / 200000000) (1384482847 / 1000000000) (Real.log (6238688277 / 1562500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (6238688277 / 1562500000) = -Real.log (1562500000 / 6238688277) := by
    rw [show ((6238688277 / 1562500000) : ℝ) = ((1562500000 / 6238688277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1016152623 / 1000000000) ≤ -Real.log (500000000000 / 1381272869223) ∧
    -Real.log (500000000000 / 1381272869223) ≤ (8129221 / 8000000) := by
  have h := checkLog_sound (w := (381272869223 / 2381272869223)) (n := 12)
    (lo := (323005443 / 1000000000)) (hi := (80751361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381272869223 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1381272869223 / 1000000000000) = 1/(500000000000 / 1381272869223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1016152623 / 1000000000) (8129221 / 8000000) (Real.log (1381272869223 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1381272869223 / 500000000000) = -Real.log (500000000000 / 1381272869223) := by
    rw [show ((1381272869223 / 500000000000) : ℝ) = ((500000000000 / 1381272869223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1020874979 / 1000000000) ≤ -Real.log (20000000000 / 55512446339) ∧
    -Real.log (20000000000 / 55512446339) ≤ (1020874981 / 1000000000) := by
  have h := checkLog_sound (w := (15512446339 / 95512446339)) (n := 12)
    (lo := (327727799 / 1000000000)) (hi := (1638639 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55512446339 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(55512446339 / 40000000000) = 1/(20000000000 / 55512446339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1020874979 / 1000000000) (1020874981 / 1000000000) (Real.log (55512446339 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (55512446339 / 20000000000) = -Real.log (20000000000 / 55512446339) := by
    rw [show ((55512446339 / 20000000000) : ℝ) = ((20000000000 / 55512446339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0090

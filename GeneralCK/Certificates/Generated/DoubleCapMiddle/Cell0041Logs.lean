import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0041
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

theorem reflection_log_1_neg : (381748581 / 1000000000) ≤ -Real.log (256 / 375) ∧
    -Real.log (256 / 375) ≤ (190874291 / 500000000) := by
  have h := checkLog_sound (w := (119 / 631)) (n := 12)
    (lo := (381748581 / 1000000000)) (hi := (190874291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((375 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(375 / 256) = 1/(256 / 375) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (381748581 / 1000000000) (190874291 / 500000000) (Real.log (375 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (375 / 256) = -Real.log (256 / 375) := by
    rw [show ((375 / 256) : ℝ) = ((256 / 375) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (312598259 / 500000000) ≤ -Real.log (137 / 256) ∧
    -Real.log (137 / 256) ≤ (625196519 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 393)) (n := 12)
    (lo := (312598259 / 500000000)) (hi := (625196519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 137) = 1/(137 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-625196519 / 1000000000) (-312598259 / 500000000) (Real.log (137 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (380948261 / 1000000000) ≤ -Real.log (2560 / 3747) ∧
    -Real.log (2560 / 3747) ≤ (190474131 / 500000000) := by
  have h := checkLog_sound (w := (1187 / 6307)) (n := 12)
    (lo := (380948261 / 1000000000)) (hi := (190474131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3747 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3747 / 2560) = 1/(2560 / 3747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (380948261 / 1000000000) (190474131 / 500000000) (Real.log (3747 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3747 / 2560) = -Real.log (2560 / 3747) := by
    rw [show ((3747 / 2560) : ℝ) = ((2560 / 3747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (623009131 / 1000000000) ≤ -Real.log (1373 / 2560) ∧
    -Real.log (1373 / 2560) ≤ (155752283 / 250000000) := by
  have h := checkLog_sound (w := (1187 / 3933)) (n := 12)
    (lo := (623009131 / 1000000000)) (hi := (155752283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1373) = 1/(1373 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-155752283 / 250000000) (-623009131 / 1000000000) (Real.log (1373 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (82169759 / 125000000) ≤ -Real.log (128 / 247) ∧
    -Real.log (128 / 247) ≤ (657358073 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 375)) (n := 12)
    (lo := (82169759 / 125000000)) (hi := (657358073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247 / 128) = 1/(128 / 247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (82169759 / 125000000) (657358073 / 1000000000) (Real.log (247 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (247 / 128) = -Real.log (128 / 247) := by
    rw [show ((247 / 128) : ℝ) = ((128 / 247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (663701421 / 250000000) ≤ -Real.log (9 / 128) ∧
    -Real.log (9 / 128) ≤ (331850711 / 125000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 9) = 1/(9 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-331850711 / 125000000) (-663701421 / 250000000) (Real.log (9 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (656142759 / 1000000000) ≤ -Real.log (1280 / 2467) ∧
    -Real.log (1280 / 2467) ≤ (16403569 / 25000000) := by
  have h := checkLog_sound (w := (1187 / 3747)) (n := 12)
    (lo := (656142759 / 1000000000)) (hi := (16403569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2467 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2467 / 1280) = 1/(1280 / 2467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (656142759 / 1000000000) (16403569 / 25000000) (Real.log (2467 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2467 / 1280) = -Real.log (1280 / 2467) := by
    rw [show ((2467 / 1280) : ℝ) = ((1280 / 2467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1311007931 / 500000000) ≤ -Real.log (93 / 1280) ∧
    -Real.log (93 / 1280) ≤ (1311007933 / 500000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 93) = 1/(93 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1311007933 / 500000000) (-1311007931 / 500000000) (Real.log (93 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (105865481 / 200000000) ≤ -Real.log (100000 / 169779) ∧
    -Real.log (100000 / 169779) ≤ (264663703 / 500000000) := by
  have h := checkLog_sound (w := (69779 / 269779)) (n := 12)
    (lo := (105865481 / 200000000)) (hi := (264663703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169779 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169779 / 100000) = 1/(100000 / 169779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (105865481 / 200000000) (264663703 / 500000000) (Real.log (169779 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (169779 / 100000) = -Real.log (100000 / 169779) := by
    rw [show ((169779 / 100000) : ℝ) = ((100000 / 169779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (598316569 / 500000000) ≤ -Real.log (30221 / 100000) ∧
    -Real.log (30221 / 100000) ≤ (59831657 / 50000000) := by
  have h := checkLog_sound (w := (19779 / 80221)) (n := 12)
    (lo := (251742979 / 500000000)) (hi := (503485959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30221) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 30221) = 1/(30221 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-59831657 / 50000000) (-598316569 / 500000000) (Real.log (30221 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (26532089 / 50000000) ≤ -Real.log (1000000 / 1700023) ∧
    -Real.log (1000000 / 1700023) ≤ (530641781 / 1000000000) := by
  have h := checkLog_sound (w := (700023 / 2700023)) (n := 12)
    (lo := (26532089 / 50000000)) (hi := (530641781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1700023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1700023 / 1000000) = 1/(1000000 / 1700023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (26532089 / 50000000) (530641781 / 1000000000) (Real.log (1700023 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1700023 / 1000000) = -Real.log (1000000 / 1700023) := by
    rw [show ((1700023 / 1000000) : ℝ) = ((1000000 / 1700023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1204049473 / 1000000000) ≤ -Real.log (299977 / 1000000) ∧
    -Real.log (299977 / 1000000) ≤ (48161979 / 40000000) := by
  have h := checkLog_sound (w := (200023 / 799977)) (n := 12)
    (lo := (510902293 / 1000000000)) (hi := (255451147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 299977) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 299977) = 1/(299977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48161979 / 40000000) (-1204049473 / 1000000000) (Real.log (299977 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (225234533 / 500000000) ≤ -Real.log (125000 / 196131) ∧
    -Real.log (125000 / 196131) ≤ (450469067 / 1000000000) := by
  have h := checkLog_sound (w := (71131 / 321131)) (n := 12)
    (lo := (225234533 / 500000000)) (hi := (450469067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196131 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196131 / 125000) = 1/(125000 / 196131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (225234533 / 500000000) (450469067 / 1000000000) (Real.log (196131 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (196131 / 125000) = -Real.log (125000 / 196131) := by
    rw [show ((196131 / 125000) : ℝ) = ((125000 / 196131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (841758563 / 1000000000) ≤ -Real.log (53869 / 125000) ∧
    -Real.log (53869 / 125000) ≤ (168351713 / 200000000) := by
  have h := checkLog_sound (w := (8631 / 116369)) (n := 12)
    (lo := (148611383 / 1000000000)) (hi := (18576423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53869) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 53869) = 1/(53869 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-168351713 / 200000000) (-841758563 / 1000000000) (Real.log (53869 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (90394661 / 200000000) ≤ -Real.log (100000 / 157141) ∧
    -Real.log (100000 / 157141) ≤ (225986653 / 500000000) := by
  have h := checkLog_sound (w := (57141 / 257141)) (n := 12)
    (lo := (90394661 / 200000000)) (hi := (225986653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157141 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157141 / 100000) = 1/(100000 / 157141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (90394661 / 200000000) (225986653 / 500000000) (Real.log (157141 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (157141 / 100000) = -Real.log (100000 / 157141) := by
    rw [show ((157141 / 100000) : ℝ) = ((100000 / 157141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (847254527 / 1000000000) ≤ -Real.log (42859 / 100000) ∧
    -Real.log (42859 / 100000) ≤ (847254529 / 1000000000) := by
  have h := checkLog_sound (w := (7141 / 92859)) (n := 12)
    (lo := (154107347 / 1000000000)) (hi := (38526837 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42859) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 42859) = 1/(42859 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-847254529 / 1000000000) (-847254527 / 1000000000) (Real.log (42859 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1725960543 / 1000000000) ≤ -Real.log (500000000000 / 2808957347539) ∧
    -Real.log (500000000000 / 2808957347539) ≤ (862980273 / 500000000) := by
  have h := checkLog_sound (w := (808957347539 / 4808957347539)) (n := 12)
    (lo := (339666183 / 1000000000)) (hi := (42458273 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2808957347539 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2808957347539 / 2000000000000) = 1/(500000000000 / 2808957347539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1725960543 / 1000000000) (862980273 / 500000000) (Real.log (2808957347539 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2808957347539 / 500000000000) = -Real.log (500000000000 / 2808957347539) := by
    rw [show ((2808957347539 / 500000000000) : ℝ) = ((500000000000 / 2808957347539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1734691253 / 1000000000) ≤ -Real.log (500000000000 / 2833588908483) ∧
    -Real.log (500000000000 / 2833588908483) ≤ (216836407 / 125000000) := by
  have h := checkLog_sound (w := (833588908483 / 4833588908483)) (n := 12)
    (lo := (348396893 / 1000000000)) (hi := (174198447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2833588908483 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2833588908483 / 2000000000000) = 1/(500000000000 / 2833588908483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1734691253 / 1000000000) (216836407 / 125000000) (Real.log (2833588908483 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2833588908483 / 500000000000) = -Real.log (500000000000 / 2833588908483) := by
    rw [show ((2833588908483 / 500000000000) : ℝ) = ((500000000000 / 2833588908483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1292227629 / 1000000000) ≤ -Real.log (500000000000 / 1820444040171) ∧
    -Real.log (500000000000 / 1820444040171) ≤ (1292227631 / 1000000000) := by
  have h := checkLog_sound (w := (820444040171 / 2820444040171)) (n := 12)
    (lo := (599080449 / 1000000000)) (hi := (11981609 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1820444040171 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1820444040171 / 1000000000000) = 1/(500000000000 / 1820444040171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1292227629 / 1000000000) (1292227631 / 1000000000) (Real.log (1820444040171 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1820444040171 / 500000000000) = -Real.log (500000000000 / 1820444040171) := by
    rw [show ((1820444040171 / 500000000000) : ℝ) = ((500000000000 / 1820444040171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (162403479 / 125000000) ≤ -Real.log (125000000000 / 458308056651) ∧
    -Real.log (125000000000 / 458308056651) ≤ (649613917 / 500000000) := by
  have h := checkLog_sound (w := (208308056651 / 708308056651)) (n := 12)
    (lo := (151520163 / 250000000)) (hi := (606080653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((458308056651 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(458308056651 / 250000000000) = 1/(125000000000 / 458308056651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (162403479 / 125000000) (649613917 / 500000000) (Real.log (458308056651 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (458308056651 / 125000000000) = -Real.log (125000000000 / 458308056651) := by
    rw [show ((458308056651 / 125000000000) : ℝ) = ((125000000000 / 458308056651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0041

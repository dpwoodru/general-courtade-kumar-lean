import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell047
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

theorem reflection_log_1_neg : (3067427 / 12500000) ≤ -Real.log (320 / 409) ∧
    -Real.log (320 / 409) ≤ (245394161 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 729)) (n := 12)
    (lo := (3067427 / 12500000)) (hi := (245394161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409 / 320) = 1/(320 / 409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (3067427 / 12500000) (245394161 / 1000000000) (Real.log (409 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (409 / 320) = -Real.log (320 / 409) := by
    rw [show ((409 / 320) : ℝ) = ((320 / 409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (65180657 / 200000000) ≤ -Real.log (231 / 320) ∧
    -Real.log (231 / 320) ≤ (162951643 / 500000000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 231) = 1/(231 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-162951643 / 500000000) (-65180657 / 200000000) (Real.log (231 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (244935619 / 1000000000) ≤ -Real.log (5120 / 6541) ∧
    -Real.log (5120 / 6541) ≤ (12246781 / 50000000) := by
  have h := checkLog_sound (w := (1421 / 11661)) (n := 12)
    (lo := (244935619 / 1000000000)) (hi := (12246781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6541 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6541 / 5120) = 1/(5120 / 6541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (244935619 / 1000000000) (12246781 / 50000000) (Real.log (6541 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6541 / 5120) = -Real.log (5120 / 6541) := by
    rw [show ((6541 / 5120) : ℝ) = ((5120 / 6541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (162545963 / 500000000) ≤ -Real.log (3699 / 5120) ∧
    -Real.log (3699 / 5120) ≤ (325091927 / 1000000000) := by
  have h := checkLog_sound (w := (1421 / 8819)) (n := 12)
    (lo := (162545963 / 500000000)) (hi := (325091927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3699) = 1/(3699 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-325091927 / 1000000000) (-162545963 / 500000000) (Real.log (3699 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1123343 / 6250000) ≤ -Real.log (10000 / 11969) ∧
    -Real.log (10000 / 11969) ≤ (179734881 / 1000000000) := by
  have h := checkLog_sound (w := (1969 / 21969)) (n := 12)
    (lo := (1123343 / 6250000)) (hi := (179734881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11969 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11969 / 10000) = 1/(10000 / 11969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1123343 / 6250000) (179734881 / 1000000000) (Real.log (11969 / 10000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11969 / 10000) = -Real.log (10000 / 11969) := by
    rw [show ((11969 / 10000) : ℝ) = ((10000 / 11969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (219276039 / 1000000000) ≤ -Real.log (8031 / 10000) ∧
    -Real.log (8031 / 10000) ≤ (5481901 / 25000000) := by
  have h := checkLog_sound (w := (1969 / 18031)) (n := 12)
    (lo := (219276039 / 1000000000)) (hi := (5481901 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8031) = 1/(8031 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5481901 / 25000000) (-219276039 / 1000000000) (Real.log (8031 / 10000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (7203429 / 40000000) ≤ -Real.log (25000 / 29933) ∧
    -Real.log (25000 / 29933) ≤ (90042863 / 500000000) := by
  have h := checkLog_sound (w := (4933 / 54933)) (n := 12)
    (lo := (7203429 / 40000000)) (hi := (90042863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29933 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29933 / 25000) = 1/(25000 / 29933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (7203429 / 40000000) (90042863 / 500000000) (Real.log (29933 / 25000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (29933 / 25000) = -Real.log (25000 / 29933) := by
    rw [show ((29933 / 25000) : ℝ) = ((25000 / 29933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4395983 / 20000000) ≤ -Real.log (20067 / 25000) ∧
    -Real.log (20067 / 25000) ≤ (219799151 / 1000000000) := by
  have h := checkLog_sound (w := (4933 / 45067)) (n := 12)
    (lo := (4395983 / 20000000)) (hi := (219799151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20067) = 1/(20067 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-219799151 / 1000000000) (-4395983 / 20000000) (Real.log (20067 / 25000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131678051 / 1000000000) ≤ -Real.log (1000000 / 1140741) ∧
    -Real.log (1000000 / 1140741) ≤ (32919513 / 250000000) := by
  have h := checkLog_sound (w := (140741 / 2140741)) (n := 12)
    (lo := (131678051 / 1000000000)) (hi := (32919513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1140741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1140741 / 1000000) = 1/(1000000 / 1140741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131678051 / 1000000000) (32919513 / 250000000) (Real.log (1140741 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1140741 / 1000000) = -Real.log (1000000 / 1140741) := by
    rw [show ((1140741 / 1000000) : ℝ) = ((1000000 / 1140741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (151684889 / 1000000000) ≤ -Real.log (859259 / 1000000) ∧
    -Real.log (859259 / 1000000) ≤ (15168489 / 100000000) := by
  have h := checkLog_sound (w := (140741 / 1859259)) (n := 12)
    (lo := (151684889 / 1000000000)) (hi := (15168489 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 859259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 859259) = 1/(859259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-15168489 / 100000000) (-151684889 / 1000000000) (Real.log (859259 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (65973569 / 500000000) ≤ -Real.log (125000 / 142631) ∧
    -Real.log (125000 / 142631) ≤ (131947139 / 1000000000) := by
  have h := checkLog_sound (w := (17631 / 267631)) (n := 12)
    (lo := (65973569 / 500000000)) (hi := (131947139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142631 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142631 / 125000) = 1/(125000 / 142631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (65973569 / 500000000) (131947139 / 1000000000) (Real.log (142631 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (142631 / 125000) = -Real.log (125000 / 142631) := by
    rw [show ((142631 / 125000) : ℝ) = ((125000 / 142631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (152042237 / 1000000000) ≤ -Real.log (107369 / 125000) ∧
    -Real.log (107369 / 125000) ≤ (76021119 / 500000000) := by
  have h := checkLog_sound (w := (17631 / 232369)) (n := 12)
    (lo := (152042237 / 1000000000)) (hi := (76021119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107369) = 1/(107369 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-76021119 / 500000000) (-152042237 / 1000000000) (Real.log (107369 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (285013773 / 500000000) ≤ -Real.log (125000000000 / 221039470127) ∧
    -Real.log (125000000000 / 221039470127) ≤ (570027547 / 1000000000) := by
  have h := checkLog_sound (w := (96039470127 / 346039470127)) (n := 12)
    (lo := (285013773 / 500000000)) (hi := (570027547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221039470127 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221039470127 / 125000000000) = 1/(125000000000 / 221039470127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (285013773 / 500000000) (570027547 / 1000000000) (Real.log (221039470127 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (221039470127 / 125000000000) = -Real.log (125000000000 / 221039470127) := by
    rw [show ((221039470127 / 125000000000) : ℝ) = ((125000000000 / 221039470127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (114259489 / 200000000) ≤ -Real.log (250000000000 / 442640692641) ∧
    -Real.log (250000000000 / 442640692641) ≤ (285648723 / 500000000) := by
  have h := checkLog_sound (w := (192640692641 / 692640692641)) (n := 12)
    (lo := (114259489 / 200000000)) (hi := (285648723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((442640692641 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(442640692641 / 250000000000) = 1/(250000000000 / 442640692641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (114259489 / 200000000) (285648723 / 500000000) (Real.log (442640692641 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (442640692641 / 250000000000) = -Real.log (250000000000 / 442640692641) := by
    rw [show ((442640692641 / 250000000000) : ℝ) = ((250000000000 / 442640692641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (9975273 / 25000000) ≤ -Real.log (12500000000 / 18629373677) ∧
    -Real.log (12500000000 / 18629373677) ≤ (399010921 / 1000000000) := by
  have h := checkLog_sound (w := (6129373677 / 31129373677)) (n := 12)
    (lo := (9975273 / 25000000)) (hi := (399010921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18629373677 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18629373677 / 12500000000) = 1/(12500000000 / 18629373677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (9975273 / 25000000) (399010921 / 1000000000) (Real.log (18629373677 / 12500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (18629373677 / 12500000000) = -Real.log (12500000000 / 18629373677) := by
    rw [show ((18629373677 / 12500000000) : ℝ) = ((12500000000 / 18629373677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3199079 / 8000000) ≤ -Real.log (62500000000 / 93228310161) ∧
    -Real.log (62500000000 / 93228310161) ≤ (99971219 / 250000000) := by
  have h := checkLog_sound (w := (30728310161 / 155728310161)) (n := 12)
    (lo := (3199079 / 8000000)) (hi := (99971219 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93228310161 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93228310161 / 62500000000) = 1/(62500000000 / 93228310161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (3199079 / 8000000) (99971219 / 250000000) (Real.log (93228310161 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (93228310161 / 62500000000) = -Real.log (62500000000 / 93228310161) := by
    rw [show ((93228310161 / 62500000000) : ℝ) = ((62500000000 / 93228310161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14168147 / 50000000) ≤ -Real.log (976562500 / 1296471591) ∧
    -Real.log (976562500 / 1296471591) ≤ (283362941 / 1000000000) := by
  have h := checkLog_sound (w := (319909091 / 2273034091)) (n := 12)
    (lo := (14168147 / 50000000)) (hi := (283362941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1296471591 / 976562500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1296471591 / 976562500) = 1/(976562500 / 1296471591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14168147 / 50000000) (283362941 / 1000000000) (Real.log (1296471591 / 976562500)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1296471591 / 976562500) = -Real.log (976562500 / 1296471591) := by
    rw [show ((1296471591 / 976562500) : ℝ) = ((976562500 / 1296471591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (454383 / 1600000) ≤ -Real.log (20000000000 / 26568376347) ∧
    -Real.log (20000000000 / 26568376347) ≤ (2218667 / 7812500) := by
  have h := checkLog_sound (w := (6568376347 / 46568376347)) (n := 12)
    (lo := (454383 / 1600000)) (hi := (2218667 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26568376347 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26568376347 / 20000000000) = 1/(20000000000 / 26568376347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (454383 / 1600000) (2218667 / 7812500) (Real.log (26568376347 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (26568376347 / 20000000000) = -Real.log (20000000000 / 26568376347) := by
    rw [show ((26568376347 / 20000000000) : ℝ) = ((20000000000 / 26568376347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20095099 / 1000000000) ≤ -Real.log (15314147839 / 15625000000) ∧
    -Real.log (15314147839 / 15625000000) ≤ (200951 / 10000000) := by
  have h := checkLog_sound (w := (310852161 / 30939147839)) (n := 12)
    (lo := (20095099 / 1000000000)) (hi := (200951 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15314147839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15314147839) = 1/(15314147839 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-200951 / 10000000) (-20095099 / 1000000000) (Real.log (15314147839 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20006837 / 1000000000) ≤ -Real.log (980191970919 / 1000000000000) ∧
    -Real.log (980191970919 / 1000000000000) ≤ (10003419 / 500000000) := by
  have h := checkLog_sound (w := (19808029081 / 1980191970919)) (n := 12)
    (lo := (20006837 / 1000000000)) (hi := (10003419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980191970919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980191970919) = 1/(980191970919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10003419 / 500000000) (-20006837 / 1000000000) (Real.log (980191970919 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell047

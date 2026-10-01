import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0462
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

theorem reflection_log_1_neg : (185246961 / 1000000000) ≤ -Real.log (2560 / 3081) ∧
    -Real.log (2560 / 3081) ≤ (92623481 / 500000000) := by
  have h := checkLog_sound (w := (521 / 5641)) (n := 12)
    (lo := (185246961 / 1000000000)) (hi := (92623481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3081 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3081 / 2560) = 1/(2560 / 3081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (185246961 / 1000000000) (92623481 / 500000000) (Real.log (3081 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3081 / 2560) = -Real.log (2560 / 3081) := by
    rw [show ((3081 / 2560) : ℝ) = ((2560 / 3081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (113773883 / 500000000) ≤ -Real.log (2039 / 2560) ∧
    -Real.log (2039 / 2560) ≤ (227547767 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 4599)) (n := 12)
    (lo := (113773883 / 500000000)) (hi := (227547767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2039) = 1/(2039 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-227547767 / 1000000000) (-113773883 / 500000000) (Real.log (2039 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11562719 / 62500000) ≤ -Real.log (10240 / 12321) ∧
    -Real.log (10240 / 12321) ≤ (37000701 / 200000000) := by
  have h := checkLog_sound (w := (2081 / 22561)) (n := 12)
    (lo := (11562719 / 62500000)) (hi := (37000701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12321 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12321 / 10240) = 1/(10240 / 12321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11562719 / 62500000) (37000701 / 200000000) (Real.log (12321 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12321 / 10240) = -Real.log (10240 / 12321) := by
    rw [show ((12321 / 10240) : ℝ) = ((10240 / 12321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (227180007 / 1000000000) ≤ -Real.log (8159 / 10240) ∧
    -Real.log (8159 / 10240) ≤ (28397501 / 125000000) := by
  have h := checkLog_sound (w := (2081 / 18399)) (n := 12)
    (lo := (227180007 / 1000000000)) (hi := (28397501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8159) = 1/(8159 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-28397501 / 125000000) (-227180007 / 1000000000) (Real.log (8159 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (85370497 / 250000000) ≤ -Real.log (1280 / 1801) ∧
    -Real.log (1280 / 1801) ≤ (341481989 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 3081)) (n := 12)
    (lo := (85370497 / 250000000)) (hi := (341481989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1801 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1801 / 1280) = 1/(1280 / 1801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (85370497 / 250000000) (341481989 / 1000000000) (Real.log (1801 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1801 / 1280) = -Real.log (1280 / 1801) := by
    rw [show ((1801 / 1280) : ℝ) = ((1280 / 1801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (522613579 / 1000000000) ≤ -Real.log (759 / 1280) ∧
    -Real.log (759 / 1280) ≤ (26130679 / 50000000) := by
  have h := checkLog_sound (w := (521 / 2039)) (n := 12)
    (lo := (522613579 / 1000000000)) (hi := (26130679 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 759) = 1/(759 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26130679 / 50000000) (-522613579 / 1000000000) (Real.log (759 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (170532733 / 500000000) ≤ -Real.log (5120 / 7201) ∧
    -Real.log (5120 / 7201) ≤ (341065467 / 1000000000) := by
  have h := checkLog_sound (w := (2081 / 12321)) (n := 12)
    (lo := (170532733 / 500000000)) (hi := (341065467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7201 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7201 / 5120) = 1/(5120 / 7201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (170532733 / 500000000) (341065467 / 1000000000) (Real.log (7201 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7201 / 5120) = -Real.log (5120 / 7201) := by
    rw [show ((7201 / 5120) : ℝ) = ((5120 / 7201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (20865037 / 40000000) ≤ -Real.log (3039 / 5120) ∧
    -Real.log (3039 / 5120) ≤ (260812963 / 500000000) := by
  have h := checkLog_sound (w := (2081 / 8159)) (n := 12)
    (lo := (20865037 / 40000000)) (hi := (260812963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3039) = 1/(3039 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-260812963 / 500000000) (-20865037 / 40000000) (Real.log (3039 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (63568871 / 250000000) ≤ -Real.log (1000000 / 1289527) ∧
    -Real.log (1000000 / 1289527) ≤ (50855097 / 200000000) := by
  have h := checkLog_sound (w := (289527 / 2289527)) (n := 12)
    (lo := (63568871 / 250000000)) (hi := (50855097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289527 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289527 / 1000000) = 1/(1000000 / 1289527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (63568871 / 250000000) (50855097 / 200000000) (Real.log (1289527 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1289527 / 1000000) = -Real.log (1000000 / 1289527) := by
    rw [show ((1289527 / 1000000) : ℝ) = ((1000000 / 1289527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (341824333 / 1000000000) ≤ -Real.log (710473 / 1000000) ∧
    -Real.log (710473 / 1000000) ≤ (170912167 / 500000000) := by
  have h := checkLog_sound (w := (289527 / 1710473)) (n := 12)
    (lo := (341824333 / 1000000000)) (hi := (170912167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 710473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 710473) = 1/(710473 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-170912167 / 500000000) (-341824333 / 1000000000) (Real.log (710473 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15912813 / 62500000) ≤ -Real.log (31250 / 40311) ∧
    -Real.log (31250 / 40311) ≤ (254605009 / 1000000000) := by
  have h := checkLog_sound (w := (9061 / 71561)) (n := 12)
    (lo := (15912813 / 62500000)) (hi := (254605009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40311 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40311 / 31250) = 1/(31250 / 40311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15912813 / 62500000) (254605009 / 1000000000) (Real.log (40311 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (40311 / 31250) = -Real.log (31250 / 40311) := by
    rw [show ((40311 / 31250) : ℝ) = ((31250 / 40311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (68484541 / 200000000) ≤ -Real.log (22189 / 31250) ∧
    -Real.log (22189 / 31250) ≤ (171211353 / 500000000) := by
  have h := checkLog_sound (w := (9061 / 53439)) (n := 12)
    (lo := (68484541 / 200000000)) (hi := (171211353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 22189) = 1/(22189 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-171211353 / 500000000) (-68484541 / 200000000) (Real.log (22189 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (38056457 / 200000000) ≤ -Real.log (1000000 / 1209591) ∧
    -Real.log (1000000 / 1209591) ≤ (95141143 / 500000000) := by
  have h := checkLog_sound (w := (209591 / 2209591)) (n := 12)
    (lo := (38056457 / 200000000)) (hi := (95141143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209591 / 1000000) = 1/(1000000 / 1209591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (38056457 / 200000000) (95141143 / 500000000) (Real.log (1209591 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1209591 / 1000000) = -Real.log (1000000 / 1209591) := by
    rw [show ((1209591 / 1000000) : ℝ) = ((1000000 / 1209591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (47040949 / 200000000) ≤ -Real.log (790409 / 1000000) ∧
    -Real.log (790409 / 1000000) ≤ (117602373 / 500000000) := by
  have h := checkLog_sound (w := (209591 / 1790409)) (n := 12)
    (lo := (47040949 / 200000000)) (hi := (117602373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790409) = 1/(790409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-117602373 / 500000000) (-47040949 / 200000000) (Real.log (790409 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (95274641 / 500000000) ≤ -Real.log (500000 / 604957) ∧
    -Real.log (500000 / 604957) ≤ (190549283 / 1000000000) := by
  have h := checkLog_sound (w := (104957 / 1104957)) (n := 12)
    (lo := (95274641 / 500000000)) (hi := (190549283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604957 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604957 / 500000) = 1/(500000 / 604957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (95274641 / 500000000) (190549283 / 1000000000) (Real.log (604957 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (604957 / 500000) = -Real.log (500000 / 604957) := by
    rw [show ((604957 / 500000) : ℝ) = ((500000 / 604957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (117806739 / 500000000) ≤ -Real.log (395043 / 500000) ∧
    -Real.log (395043 / 500000) ≤ (235613479 / 1000000000) := by
  have h := checkLog_sound (w := (104957 / 895043)) (n := 12)
    (lo := (117806739 / 500000000)) (hi := (235613479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 395043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 395043) = 1/(395043 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-235613479 / 1000000000) (-117806739 / 500000000) (Real.log (395043 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (298049909 / 500000000) ≤ -Real.log (250000000000 / 453756511507) ∧
    -Real.log (250000000000 / 453756511507) ≤ (596099819 / 1000000000) := by
  have h := checkLog_sound (w := (203756511507 / 703756511507)) (n := 12)
    (lo := (298049909 / 500000000)) (hi := (596099819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((453756511507 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(453756511507 / 250000000000) = 1/(250000000000 / 453756511507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (298049909 / 500000000) (596099819 / 1000000000) (Real.log (453756511507 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (453756511507 / 250000000000) = -Real.log (250000000000 / 453756511507) := by
    rw [show ((453756511507 / 250000000000) : ℝ) = ((250000000000 / 453756511507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (597027713 / 1000000000) ≤ -Real.log (25000000000 / 45417774573) ∧
    -Real.log (25000000000 / 45417774573) ≤ (298513857 / 500000000) := by
  have h := checkLog_sound (w := (20417774573 / 70417774573)) (n := 12)
    (lo := (597027713 / 1000000000)) (hi := (298513857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45417774573 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45417774573 / 25000000000) = 1/(25000000000 / 45417774573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (597027713 / 1000000000) (298513857 / 500000000) (Real.log (45417774573 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (45417774573 / 25000000000) = -Real.log (25000000000 / 45417774573) := by
    rw [show ((45417774573 / 25000000000) : ℝ) = ((25000000000 / 45417774573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (425487031 / 1000000000) ≤ -Real.log (20000000000 / 30606711209) ∧
    -Real.log (20000000000 / 30606711209) ≤ (53185879 / 125000000) := by
  have h := checkLog_sound (w := (10606711209 / 50606711209)) (n := 12)
    (lo := (425487031 / 1000000000)) (hi := (53185879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30606711209 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30606711209 / 20000000000) = 1/(20000000000 / 30606711209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (425487031 / 1000000000) (53185879 / 125000000) (Real.log (30606711209 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (30606711209 / 20000000000) = -Real.log (20000000000 / 30606711209) := by
    rw [show ((30606711209 / 20000000000) : ℝ) = ((20000000000 / 30606711209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (426162761 / 1000000000) ≤ -Real.log (25000000000 / 38284250069) ∧
    -Real.log (25000000000 / 38284250069) ≤ (213081381 / 500000000) := by
  have h := checkLog_sound (w := (13284250069 / 63284250069)) (n := 12)
    (lo := (426162761 / 1000000000)) (hi := (213081381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38284250069 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38284250069 / 25000000000) = 1/(25000000000 / 38284250069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (426162761 / 1000000000) (213081381 / 500000000) (Real.log (38284250069 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (38284250069 / 25000000000) = -Real.log (25000000000 / 38284250069) := by
    rw [show ((38284250069 / 25000000000) : ℝ) = ((25000000000 / 38284250069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0462

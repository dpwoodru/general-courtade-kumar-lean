import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0437
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

theorem reflection_log_1_neg : (47828551 / 250000000) ≤ -Real.log (10240 / 12399) ∧
    -Real.log (10240 / 12399) ≤ (38262841 / 200000000) := by
  have h := checkLog_sound (w := (2159 / 22639)) (n := 12)
    (lo := (47828551 / 250000000)) (hi := (38262841 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12399 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12399 / 10240) = 1/(10240 / 12399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (47828551 / 250000000) (38262841 / 200000000) (Real.log (12399 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12399 / 10240) = -Real.log (10240 / 12399) := by
    rw [show ((12399 / 10240) : ℝ) = ((10240 / 12399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (29598249 / 125000000) ≤ -Real.log (8081 / 10240) ∧
    -Real.log (8081 / 10240) ≤ (236785993 / 1000000000) := by
  have h := checkLog_sound (w := (2159 / 18321)) (n := 12)
    (lo := (29598249 / 125000000)) (hi := (236785993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8081) = 1/(8081 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-236785993 / 1000000000) (-29598249 / 125000000) (Real.log (8081 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (9553611 / 50000000) ≤ -Real.log (2560 / 3099) ∧
    -Real.log (2560 / 3099) ≤ (191072221 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 5659)) (n := 12)
    (lo := (9553611 / 50000000)) (hi := (191072221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3099 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3099 / 2560) = 1/(2560 / 3099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (9553611 / 50000000) (191072221 / 1000000000) (Real.log (3099 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3099 / 2560) = -Real.log (2560 / 3099) := by
    rw [show ((3099 / 2560) : ℝ) = ((2560 / 3099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (11820741 / 50000000) ≤ -Real.log (2021 / 2560) ∧
    -Real.log (2021 / 2560) ≤ (236414821 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 4581)) (n := 12)
    (lo := (11820741 / 50000000)) (hi := (236414821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2021) = 1/(2021 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-236414821 / 1000000000) (-11820741 / 50000000) (Real.log (2021 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (351839051 / 1000000000) ≤ -Real.log (5120 / 7279) ∧
    -Real.log (5120 / 7279) ≤ (87959763 / 250000000) := by
  have h := checkLog_sound (w := (2159 / 12399)) (n := 12)
    (lo := (351839051 / 1000000000)) (hi := (87959763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7279 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7279 / 5120) = 1/(5120 / 7279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (351839051 / 1000000000) (87959763 / 250000000) (Real.log (7279 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7279 / 5120) = -Real.log (5120 / 7279) := by
    rw [show ((7279 / 5120) : ℝ) = ((5120 / 7279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (547627389 / 1000000000) ≤ -Real.log (2961 / 5120) ∧
    -Real.log (2961 / 5120) ≤ (54762739 / 100000000) := by
  have h := checkLog_sound (w := (2159 / 8081)) (n := 12)
    (lo := (547627389 / 1000000000)) (hi := (54762739 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2961) = 1/(2961 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-54762739 / 100000000) (-547627389 / 1000000000) (Real.log (2961 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (351426821 / 1000000000) ≤ -Real.log (1280 / 1819) ∧
    -Real.log (1280 / 1819) ≤ (175713411 / 500000000) := by
  have h := checkLog_sound (w := (539 / 3099)) (n := 12)
    (lo := (351426821 / 1000000000)) (hi := (175713411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1819 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1819 / 1280) = 1/(1280 / 1819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (351426821 / 1000000000) (175713411 / 500000000) (Real.log (1819 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1819 / 1280) = -Real.log (1280 / 1819) := by
    rw [show ((1819 / 1280) : ℝ) = ((1280 / 1819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (546614731 / 1000000000) ≤ -Real.log (741 / 1280) ∧
    -Real.log (741 / 1280) ≤ (136653683 / 250000000) := by
  have h := checkLog_sound (w := (539 / 2021)) (n := 12)
    (lo := (546614731 / 1000000000)) (hi := (136653683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 741) = 1/(741 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-136653683 / 250000000) (-546614731 / 1000000000) (Real.log (741 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131234437 / 500000000) ≤ -Real.log (125000 / 162517) ∧
    -Real.log (125000 / 162517) ≤ (2099751 / 8000000) := by
  have h := checkLog_sound (w := (37517 / 287517)) (n := 12)
    (lo := (131234437 / 500000000)) (hi := (2099751 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162517 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162517 / 125000) = 1/(125000 / 162517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131234437 / 500000000) (2099751 / 8000000) (Real.log (162517 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (162517 / 125000) = -Real.log (125000 / 162517) := by
    rw [show ((162517 / 125000) : ℝ) = ((125000 / 162517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2788041 / 7812500) ≤ -Real.log (87483 / 125000) ∧
    -Real.log (87483 / 125000) ≤ (356869249 / 1000000000) := by
  have h := checkLog_sound (w := (37517 / 212483)) (n := 12)
    (lo := (2788041 / 7812500)) (hi := (356869249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 87483) = 1/(87483 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-356869249 / 1000000000) (-2788041 / 7812500) (Real.log (87483 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (131398239 / 500000000) ≤ -Real.log (500000 / 650281) ∧
    -Real.log (500000 / 650281) ≤ (262796479 / 1000000000) := by
  have h := checkLog_sound (w := (150281 / 1150281)) (n := 12)
    (lo := (131398239 / 500000000)) (hi := (262796479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650281 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650281 / 500000) = 1/(500000 / 650281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (131398239 / 500000000) (262796479 / 1000000000) (Real.log (650281 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (650281 / 500000) = -Real.log (500000 / 650281) := by
    rw [show ((650281 / 500000) : ℝ) = ((500000 / 650281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (357478123 / 1000000000) ≤ -Real.log (349719 / 500000) ∧
    -Real.log (349719 / 500000) ≤ (89369531 / 250000000) := by
  have h := checkLog_sound (w := (150281 / 849719)) (n := 12)
    (lo := (357478123 / 1000000000)) (hi := (89369531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 349719) = 1/(349719 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89369531 / 250000000) (-357478123 / 1000000000) (Real.log (349719 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4923213 / 25000000) ≤ -Real.log (1000000 / 1217657) ∧
    -Real.log (1000000 / 1217657) ≤ (196928521 / 1000000000) := by
  have h := checkLog_sound (w := (217657 / 2217657)) (n := 12)
    (lo := (4923213 / 25000000)) (hi := (196928521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217657 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217657 / 1000000) = 1/(1000000 / 1217657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4923213 / 25000000) (196928521 / 1000000000) (Real.log (1217657 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1217657 / 1000000) = -Real.log (1000000 / 1217657) := by
    rw [show ((1217657 / 1000000) : ℝ) = ((1000000 / 1217657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49092403 / 200000000) ≤ -Real.log (782343 / 1000000) ∧
    -Real.log (782343 / 1000000) ≤ (479418 / 1953125) := by
  have h := checkLog_sound (w := (217657 / 1782343)) (n := 12)
    (lo := (49092403 / 200000000)) (hi := (479418 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782343) = 1/(782343 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-479418 / 1953125) (-49092403 / 200000000) (Real.log (782343 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19719539 / 100000000) ≤ -Real.log (500000 / 608991) ∧
    -Real.log (500000 / 608991) ≤ (197195391 / 1000000000) := by
  have h := checkLog_sound (w := (108991 / 1108991)) (n := 12)
    (lo := (19719539 / 100000000)) (hi := (197195391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608991 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608991 / 500000) = 1/(500000 / 608991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19719539 / 100000000) (197195391 / 1000000000) (Real.log (608991 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (608991 / 500000) = -Real.log (500000 / 608991) := by
    rw [show ((608991 / 500000) : ℝ) = ((500000 / 608991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3073469 / 12500000) ≤ -Real.log (391009 / 500000) ∧
    -Real.log (391009 / 500000) ≤ (245877521 / 1000000000) := by
  have h := checkLog_sound (w := (108991 / 891009)) (n := 12)
    (lo := (3073469 / 12500000)) (hi := (245877521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391009) = 1/(391009 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-245877521 / 1000000000) (-3073469 / 12500000) (Real.log (391009 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (309669061 / 500000000) ≤ -Real.log (250000000000 / 464424516763) ∧
    -Real.log (250000000000 / 464424516763) ≤ (619338123 / 1000000000) := by
  have h := checkLog_sound (w := (214424516763 / 714424516763)) (n := 12)
    (lo := (309669061 / 500000000)) (hi := (619338123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((464424516763 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(464424516763 / 250000000000) = 1/(250000000000 / 464424516763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (309669061 / 500000000) (619338123 / 1000000000) (Real.log (464424516763 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (464424516763 / 250000000000) = -Real.log (250000000000 / 464424516763) := by
    rw [show ((464424516763 / 250000000000) : ℝ) = ((250000000000 / 464424516763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (310137301 / 500000000) ≤ -Real.log (100000000000 / 185943857783) ∧
    -Real.log (100000000000 / 185943857783) ≤ (620274603 / 1000000000) := by
  have h := checkLog_sound (w := (85943857783 / 285943857783)) (n := 12)
    (lo := (310137301 / 500000000)) (hi := (620274603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185943857783 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185943857783 / 100000000000) = 1/(100000000000 / 185943857783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (310137301 / 500000000) (620274603 / 1000000000) (Real.log (185943857783 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (185943857783 / 100000000000) = -Real.log (100000000000 / 185943857783) := by
    rw [show ((185943857783 / 100000000000) : ℝ) = ((100000000000 / 185943857783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (55298817 / 125000000) ≤ -Real.log (25000000000 / 38910586533) ∧
    -Real.log (25000000000 / 38910586533) ≤ (442390537 / 1000000000) := by
  have h := checkLog_sound (w := (13910586533 / 63910586533)) (n := 12)
    (lo := (55298817 / 125000000)) (hi := (442390537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38910586533 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38910586533 / 25000000000) = 1/(25000000000 / 38910586533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (55298817 / 125000000) (442390537 / 1000000000) (Real.log (38910586533 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (38910586533 / 25000000000) = -Real.log (25000000000 / 38910586533) := by
    rw [show ((38910586533 / 25000000000) : ℝ) = ((25000000000 / 38910586533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (443072911 / 1000000000) ≤ -Real.log (62500000000 / 97342868067) ∧
    -Real.log (62500000000 / 97342868067) ≤ (27692057 / 62500000) := by
  have h := checkLog_sound (w := (34842868067 / 159842868067)) (n := 12)
    (lo := (443072911 / 1000000000)) (hi := (27692057 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97342868067 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97342868067 / 62500000000) = 1/(62500000000 / 97342868067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (443072911 / 1000000000) (27692057 / 62500000) (Real.log (97342868067 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (97342868067 / 62500000000) = -Real.log (62500000000 / 97342868067) := by
    rw [show ((97342868067 / 62500000000) : ℝ) = ((62500000000 / 97342868067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0437

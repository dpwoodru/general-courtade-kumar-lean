import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0100
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

theorem reflection_log_1_neg : (4167479 / 12500000) ≤ -Real.log (2560 / 3573) ∧
    -Real.log (2560 / 3573) ≤ (333398321 / 1000000000) := by
  have h := checkLog_sound (w := (1013 / 6133)) (n := 12)
    (lo := (4167479 / 12500000)) (hi := (333398321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3573 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3573 / 2560) = 1/(2560 / 3573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (4167479 / 12500000) (333398321 / 1000000000) (Real.log (3573 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3573 / 2560) = -Real.log (2560 / 3573) := by
    rw [show ((3573 / 2560) : ℝ) = ((2560 / 3573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (251844843 / 500000000) ≤ -Real.log (1547 / 2560) ∧
    -Real.log (1547 / 2560) ≤ (503689687 / 1000000000) := by
  have h := checkLog_sound (w := (1013 / 4107)) (n := 12)
    (lo := (251844843 / 500000000)) (hi := (503689687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1547) = 1/(1547 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-503689687 / 1000000000) (-251844843 / 500000000) (Real.log (1547 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (332558337 / 1000000000) ≤ -Real.log (256 / 357) ∧
    -Real.log (256 / 357) ≤ (166279169 / 500000000) := by
  have h := checkLog_sound (w := (101 / 613)) (n := 12)
    (lo := (332558337 / 1000000000)) (hi := (166279169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357 / 256) = 1/(256 / 357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (332558337 / 1000000000) (166279169 / 500000000) (Real.log (357 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (357 / 256) = -Real.log (256 / 357) := by
    rw [show ((357 / 256) : ℝ) = ((256 / 357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (501752327 / 1000000000) ≤ -Real.log (155 / 256) ∧
    -Real.log (155 / 256) ≤ (62719041 / 125000000) := by
  have h := checkLog_sound (w := (101 / 411)) (n := 12)
    (lo := (501752327 / 1000000000)) (hi := (62719041 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 155) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 155) = 1/(155 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-62719041 / 125000000) (-501752327 / 1000000000) (Real.log (155 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23320037 / 40000000) ≤ -Real.log (1280 / 2293) ∧
    -Real.log (1280 / 2293) ≤ (291500463 / 500000000) := by
  have h := checkLog_sound (w := (1013 / 3573)) (n := 12)
    (lo := (23320037 / 40000000)) (hi := (291500463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2293 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2293 / 1280) = 1/(1280 / 2293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23320037 / 40000000) (291500463 / 500000000) (Real.log (2293 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2293 / 1280) = -Real.log (1280 / 2293) := by
    rw [show ((2293 / 1280) : ℝ) = ((1280 / 2293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1567366697 / 1000000000) ≤ -Real.log (267 / 1280) ∧
    -Real.log (267 / 1280) ≤ (15673667 / 10000000) := by
  have h := checkLog_sound (w := (53 / 587)) (n := 12)
    (lo := (181072337 / 1000000000)) (hi := (90536169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 267) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 267) = 1/(267 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-15673667 / 10000000) (-1567366697 / 1000000000) (Real.log (267 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (581691739 / 1000000000) ≤ -Real.log (128 / 229) ∧
    -Real.log (128 / 229) ≤ (29084587 / 50000000) := by
  have h := checkLog_sound (w := (101 / 357)) (n := 12)
    (lo := (581691739 / 1000000000)) (hi := (29084587 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229 / 128) = 1/(128 / 229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (581691739 / 1000000000) (29084587 / 50000000) (Real.log (229 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (229 / 128) = -Real.log (128 / 229) := by
    rw [show ((229 / 128) : ℝ) = ((128 / 229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (389048349 / 250000000) ≤ -Real.log (27 / 128) ∧
    -Real.log (27 / 128) ≤ (1556193399 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 27) = 1/(27 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1556193399 / 1000000000) (-389048349 / 250000000) (Real.log (27 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (456385699 / 1000000000) ≤ -Real.log (1000000 / 1578359) ∧
    -Real.log (1000000 / 1578359) ≤ (4563857 / 10000000) := by
  have h := checkLog_sound (w := (578359 / 2578359)) (n := 12)
    (lo := (456385699 / 1000000000)) (hi := (4563857 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1578359 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1578359 / 1000000) = 1/(1000000 / 1578359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (456385699 / 1000000000) (4563857 / 10000000) (Real.log (1578359 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1578359 / 1000000) = -Real.log (1000000 / 1578359) := by
    rw [show ((1578359 / 1000000) : ℝ) = ((1000000 / 1578359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (863601037 / 1000000000) ≤ -Real.log (421641 / 1000000) ∧
    -Real.log (421641 / 1000000) ≤ (863601039 / 1000000000) := by
  have h := checkLog_sound (w := (78359 / 921641)) (n := 12)
    (lo := (170453857 / 1000000000)) (hi := (85226929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421641) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 421641) = 1/(421641 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-863601039 / 1000000000) (-863601037 / 1000000000) (Real.log (421641 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (45758939 / 100000000) ≤ -Real.log (50000 / 79013) ∧
    -Real.log (50000 / 79013) ≤ (457589391 / 1000000000) := by
  have h := checkLog_sound (w := (29013 / 129013)) (n := 12)
    (lo := (45758939 / 100000000)) (hi := (457589391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79013 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79013 / 50000) = 1/(50000 / 79013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (45758939 / 100000000) (457589391 / 1000000000) (Real.log (79013 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (79013 / 50000) = -Real.log (50000 / 79013) := by
    rw [show ((79013 / 50000) : ℝ) = ((50000 / 79013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (434059903 / 500000000) ≤ -Real.log (20987 / 50000) ∧
    -Real.log (20987 / 50000) ≤ (3391093 / 3906250) := by
  have h := checkLog_sound (w := (4013 / 45987)) (n := 12)
    (lo := (87486313 / 500000000)) (hi := (174972627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 20987) = 1/(20987 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3391093 / 3906250) (-434059903 / 500000000) (Real.log (20987 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (37183869 / 100000000) ≤ -Real.log (1000000 / 1450399) ∧
    -Real.log (1000000 / 1450399) ≤ (371838691 / 1000000000) := by
  have h := checkLog_sound (w := (450399 / 2450399)) (n := 12)
    (lo := (37183869 / 100000000)) (hi := (371838691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1450399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1450399 / 1000000) = 1/(1000000 / 1450399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (37183869 / 100000000) (371838691 / 1000000000) (Real.log (1450399 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1450399 / 1000000) = -Real.log (1000000 / 1450399) := by
    rw [show ((1450399 / 1000000) : ℝ) = ((1000000 / 1450399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (299281359 / 500000000) ≤ -Real.log (549601 / 1000000) ∧
    -Real.log (549601 / 1000000) ≤ (598562719 / 1000000000) := by
  have h := checkLog_sound (w := (450399 / 1549601)) (n := 12)
    (lo := (299281359 / 500000000)) (hi := (598562719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 549601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 549601) = 1/(549601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-598562719 / 1000000000) (-299281359 / 500000000) (Real.log (549601 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (373063809 / 1000000000) ≤ -Real.log (1000000 / 1452177) ∧
    -Real.log (1000000 / 1452177) ≤ (37306381 / 100000000) := by
  have h := checkLog_sound (w := (452177 / 2452177)) (n := 12)
    (lo := (373063809 / 1000000000)) (hi := (37306381 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1452177 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1452177 / 1000000) = 1/(1000000 / 1452177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (373063809 / 1000000000) (37306381 / 100000000) (Real.log (1452177 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1452177 / 1000000) = -Real.log (1000000 / 1452177) := by
    rw [show ((1452177 / 1000000) : ℝ) = ((1000000 / 1452177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (150450759 / 250000000) ≤ -Real.log (547823 / 1000000) ∧
    -Real.log (547823 / 1000000) ≤ (601803037 / 1000000000) := by
  have h := checkLog_sound (w := (452177 / 1547823)) (n := 12)
    (lo := (150450759 / 250000000)) (hi := (601803037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 547823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 547823) = 1/(547823 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-601803037 / 1000000000) (-150450759 / 250000000) (Real.log (547823 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1319986737 / 1000000000) ≤ -Real.log (500000000000 / 1871685865463) ∧
    -Real.log (500000000000 / 1871685865463) ≤ (1319986739 / 1000000000) := by
  have h := checkLog_sound (w := (871685865463 / 2871685865463)) (n := 12)
    (lo := (626839557 / 1000000000)) (hi := (313419779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1871685865463 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1871685865463 / 1000000000000) = 1/(500000000000 / 1871685865463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1319986737 / 1000000000) (1319986739 / 1000000000) (Real.log (1871685865463 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1871685865463 / 500000000000) = -Real.log (500000000000 / 1871685865463) := by
    rw [show ((1871685865463 / 500000000000) : ℝ) = ((500000000000 / 1871685865463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (331427299 / 250000000) ≤ -Real.log (500000000000 / 1882427216849) ∧
    -Real.log (500000000000 / 1882427216849) ≤ (662854599 / 500000000) := by
  have h := checkLog_sound (w := (882427216849 / 2882427216849)) (n := 12)
    (lo := (19767563 / 31250000)) (hi := (632562017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1882427216849 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1882427216849 / 1000000000000) = 1/(500000000000 / 1882427216849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (331427299 / 250000000) (662854599 / 500000000) (Real.log (1882427216849 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1882427216849 / 500000000000) = -Real.log (500000000000 / 1882427216849) := by
    rw [show ((1882427216849 / 500000000000) : ℝ) = ((500000000000 / 1882427216849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (970401409 / 1000000000) ≤ -Real.log (500000000000 / 1319501784021) ∧
    -Real.log (500000000000 / 1319501784021) ≤ (970401411 / 1000000000) := by
  have h := checkLog_sound (w := (319501784021 / 2319501784021)) (n := 12)
    (lo := (277254229 / 1000000000)) (hi := (27725423 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319501784021 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1319501784021 / 1000000000000) = 1/(500000000000 / 1319501784021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (970401409 / 1000000000) (970401411 / 1000000000) (Real.log (1319501784021 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1319501784021 / 500000000000) = -Real.log (500000000000 / 1319501784021) := by
    rw [show ((1319501784021 / 500000000000) : ℝ) = ((500000000000 / 1319501784021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (487433423 / 500000000) ≤ -Real.log (250000000000 / 662703555711) ∧
    -Real.log (250000000000 / 662703555711) ≤ (30464589 / 31250000) := by
  have h := checkLog_sound (w := (162703555711 / 1162703555711)) (n := 12)
    (lo := (140859833 / 500000000)) (hi := (281719667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((662703555711 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(662703555711 / 500000000000) = 1/(250000000000 / 662703555711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (487433423 / 500000000) (30464589 / 31250000) (Real.log (662703555711 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (662703555711 / 250000000000) = -Real.log (250000000000 / 662703555711) := by
    rw [show ((662703555711 / 250000000000) : ℝ) = ((250000000000 / 662703555711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0100

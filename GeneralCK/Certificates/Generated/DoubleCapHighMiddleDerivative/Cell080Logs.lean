import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell080
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

theorem reflection_log_1_neg : (260409229 / 1000000000) ≤ -Real.log (5120 / 6643) ∧
    -Real.log (5120 / 6643) ≤ (26040923 / 100000000) := by
  have h := checkLog_sound (w := (1523 / 11763)) (n := 12)
    (lo := (260409229 / 1000000000)) (hi := (26040923 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6643 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6643 / 5120) = 1/(5120 / 6643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (260409229 / 1000000000) (26040923 / 100000000) (Real.log (6643 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6643 / 5120) = -Real.log (5120 / 6643) := by
    rw [show ((6643 / 5120) : ℝ) = ((5120 / 6643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (176527137 / 500000000) ≤ -Real.log (3597 / 5120) ∧
    -Real.log (3597 / 5120) ≤ (14122171 / 40000000) := by
  have h := checkLog_sound (w := (1523 / 8717)) (n := 12)
    (lo := (176527137 / 500000000)) (hi := (14122171 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3597) = 1/(3597 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-14122171 / 40000000) (-176527137 / 500000000) (Real.log (3597 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (64989381 / 250000000) ≤ -Real.log (64 / 83) ∧
    -Real.log (64 / 83) ≤ (10398301 / 40000000) := by
  have h := checkLog_sound (w := (19 / 147)) (n := 12)
    (lo := (64989381 / 250000000)) (hi := (10398301 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83 / 64) = 1/(64 / 83) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (64989381 / 250000000) (10398301 / 40000000) (Real.log (83 / 64)) := by
  have h := reflection_log_3_neg
  have he : Real.log (83 / 64) = -Real.log (64 / 83) := by
    rw [show ((83 / 64) : ℝ) = ((64 / 83) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (352220593 / 1000000000) ≤ -Real.log (45 / 64) ∧
    -Real.log (45 / 64) ≤ (176110297 / 500000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 45) = 1/(45 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-176110297 / 500000000) (-352220593 / 1000000000) (Real.log (45 / 64)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (305947 / 1600000) ≤ -Real.log (500000 / 605361) ∧
    -Real.log (500000 / 605361) ≤ (47804219 / 250000000) := by
  have h := checkLog_sound (w := (105361 / 1105361)) (n := 12)
    (lo := (305947 / 1600000)) (hi := (47804219 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605361 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605361 / 500000) = 1/(500000 / 605361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (305947 / 1600000) (47804219 / 250000000) (Real.log (605361 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (605361 / 500000) = -Real.log (500000 / 605361) := by
    rw [show ((605361 / 500000) : ℝ) = ((500000 / 605361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9465467 / 40000000) ≤ -Real.log (394639 / 500000) ∧
    -Real.log (394639 / 500000) ≤ (59159169 / 250000000) := by
  have h := checkLog_sound (w := (105361 / 894639)) (n := 12)
    (lo := (9465467 / 40000000)) (hi := (59159169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394639) = 1/(394639 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-59159169 / 250000000) (-9465467 / 40000000) (Real.log (394639 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (47890929 / 250000000) ≤ -Real.log (500000 / 605571) ∧
    -Real.log (500000 / 605571) ≤ (191563717 / 1000000000) := by
  have h := checkLog_sound (w := (105571 / 1105571)) (n := 12)
    (lo := (47890929 / 250000000)) (hi := (191563717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605571 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605571 / 500000) = 1/(500000 / 605571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (47890929 / 250000000) (191563717 / 1000000000) (Real.log (605571 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (605571 / 500000) = -Real.log (500000 / 605571) := by
    rw [show ((605571 / 500000) : ℝ) = ((500000 / 605571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (59292237 / 250000000) ≤ -Real.log (394429 / 500000) ∧
    -Real.log (394429 / 500000) ≤ (237168949 / 1000000000) := by
  have h := checkLog_sound (w := (105571 / 894429)) (n := 12)
    (lo := (59292237 / 250000000)) (hi := (237168949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394429) = 1/(394429 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-237168949 / 1000000000) (-59292237 / 250000000) (Real.log (394429 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (7025431 / 50000000) ≤ -Real.log (1000000 / 1150859) ∧
    -Real.log (1000000 / 1150859) ≤ (140508621 / 1000000000) := by
  have h := checkLog_sound (w := (150859 / 2150859)) (n := 12)
    (lo := (7025431 / 50000000)) (hi := (140508621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150859 / 1000000) = 1/(1000000 / 1150859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (7025431 / 50000000) (140508621 / 1000000000) (Real.log (1150859 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1150859 / 1000000) = -Real.log (1000000 / 1150859) := by
    rw [show ((1150859 / 1000000) : ℝ) = ((1000000 / 1150859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (40882507 / 250000000) ≤ -Real.log (849141 / 1000000) ∧
    -Real.log (849141 / 1000000) ≤ (163530029 / 1000000000) := by
  have h := checkLog_sound (w := (150859 / 1849141)) (n := 12)
    (lo := (40882507 / 250000000)) (hi := (163530029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849141) = 1/(849141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-163530029 / 1000000000) (-40882507 / 250000000) (Real.log (849141 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (140777079 / 1000000000) ≤ -Real.log (15625 / 17987) ∧
    -Real.log (15625 / 17987) ≤ (3519427 / 25000000) := by
  have h := checkLog_sound (w := (1181 / 16806)) (n := 12)
    (lo := (140777079 / 1000000000)) (hi := (3519427 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17987 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17987 / 15625) = 1/(15625 / 17987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (140777079 / 1000000000) (3519427 / 25000000) (Real.log (17987 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (17987 / 15625) = -Real.log (15625 / 17987) := by
    rw [show ((17987 / 15625) : ℝ) = ((15625 / 17987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (20486749 / 125000000) ≤ -Real.log (13263 / 15625) ∧
    -Real.log (13263 / 15625) ≤ (163893993 / 1000000000) := by
  have h := checkLog_sound (w := (1181 / 14444)) (n := 12)
    (lo := (20486749 / 125000000)) (hi := (163893993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13263) = 1/(13263 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-163893993 / 1000000000) (-20486749 / 125000000) (Real.log (13263 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (306089059 / 500000000) ≤ -Real.log (250000000000 / 461111111111) ∧
    -Real.log (250000000000 / 461111111111) ≤ (612178119 / 1000000000) := by
  have h := checkLog_sound (w := (211111111111 / 711111111111)) (n := 12)
    (lo := (306089059 / 500000000)) (hi := (612178119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461111111111 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461111111111 / 250000000000) = 1/(250000000000 / 461111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (306089059 / 500000000) (612178119 / 1000000000) (Real.log (461111111111 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (461111111111 / 250000000000) = -Real.log (250000000000 / 461111111111) := by
    rw [show ((461111111111 / 250000000000) : ℝ) = ((250000000000 / 461111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (613463503 / 1000000000) ≤ -Real.log (250000000000 / 461704197943) ∧
    -Real.log (250000000000 / 461704197943) ≤ (38341469 / 62500000) := by
  have h := checkLog_sound (w := (211704197943 / 711704197943)) (n := 12)
    (lo := (613463503 / 1000000000)) (hi := (38341469 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461704197943 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461704197943 / 250000000000) = 1/(250000000000 / 461704197943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (613463503 / 1000000000) (38341469 / 62500000) (Real.log (461704197943 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (461704197943 / 250000000000) = -Real.log (250000000000 / 461704197943) := by
    rw [show ((461704197943 / 250000000000) : ℝ) = ((250000000000 / 461704197943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (427853551 / 1000000000) ≤ -Real.log (500000000000 / 766980708951) ∧
    -Real.log (500000000000 / 766980708951) ≤ (26740847 / 62500000) := by
  have h := checkLog_sound (w := (266980708951 / 1266980708951)) (n := 12)
    (lo := (427853551 / 1000000000)) (hi := (26740847 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((766980708951 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(766980708951 / 500000000000) = 1/(500000000000 / 766980708951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (427853551 / 1000000000) (26740847 / 62500000) (Real.log (766980708951 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (766980708951 / 500000000000) = -Real.log (500000000000 / 766980708951) := by
    rw [show ((766980708951 / 500000000000) : ℝ) = ((500000000000 / 766980708951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (85746533 / 200000000) ≤ -Real.log (125000000000 / 191913817189) ∧
    -Real.log (125000000000 / 191913817189) ≤ (214366333 / 500000000) := by
  have h := checkLog_sound (w := (66913817189 / 316913817189)) (n := 12)
    (lo := (85746533 / 200000000)) (hi := (214366333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191913817189 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191913817189 / 125000000000) = 1/(125000000000 / 191913817189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (85746533 / 200000000) (214366333 / 500000000) (Real.log (191913817189 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (191913817189 / 125000000000) = -Real.log (125000000000 / 191913817189) := by
    rw [show ((191913817189 / 125000000000) : ℝ) = ((125000000000 / 191913817189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (38004831 / 125000000) ≤ -Real.log (250000000000 / 338830359151) ∧
    -Real.log (250000000000 / 338830359151) ≤ (304038649 / 1000000000) := by
  have h := checkLog_sound (w := (88830359151 / 588830359151)) (n := 12)
    (lo := (38004831 / 125000000)) (hi := (304038649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338830359151 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338830359151 / 250000000000) = 1/(250000000000 / 338830359151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (38004831 / 125000000) (304038649 / 1000000000) (Real.log (338830359151 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (338830359151 / 250000000000) = -Real.log (250000000000 / 338830359151) := by
    rw [show ((338830359151 / 250000000000) : ℝ) = ((250000000000 / 338830359151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (304671071 / 1000000000) ≤ -Real.log (5000000000 / 6780894217) ∧
    -Real.log (5000000000 / 6780894217) ≤ (9520971 / 31250000) := by
  have h := checkLog_sound (w := (1780894217 / 11780894217)) (n := 12)
    (lo := (304671071 / 1000000000)) (hi := (9520971 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6780894217 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6780894217 / 5000000000) = 1/(5000000000 / 6780894217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (304671071 / 1000000000) (9520971 / 31250000) (Real.log (6780894217 / 5000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (6780894217 / 5000000000) = -Real.log (5000000000 / 6780894217) := by
    rw [show ((6780894217 / 5000000000) : ℝ) = ((5000000000 / 6780894217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1444807 / 62500000) ≤ -Real.log (238561581 / 244140625) ∧
    -Real.log (238561581 / 244140625) ≤ (23116913 / 1000000000) := by
  have h := checkLog_sound (w := (2789522 / 241351103)) (n := 12)
    (lo := (1444807 / 62500000)) (hi := (23116913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 238561581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 238561581) = 1/(238561581 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23116913 / 1000000000) (-1444807 / 62500000) (Real.log (238561581 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (719419 / 31250000) ≤ -Real.log (977241562119 / 1000000000000) ∧
    -Real.log (977241562119 / 1000000000000) ≤ (23021409 / 1000000000) := by
  have h := checkLog_sound (w := (22758437881 / 1977241562119)) (n := 12)
    (lo := (719419 / 31250000)) (hi := (23021409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977241562119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977241562119) = 1/(977241562119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-23021409 / 1000000000) (-719419 / 31250000) (Real.log (977241562119 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell080

import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15552_neg : (500382483 / 1000000000) ≤ -Real.log (125000 / 206169) ∧
    -Real.log (125000 / 206169) ≤ (125095621 / 250000000) := by
  have h := checkLog_sound (w := (81169 / 331169)) (n := 12)
    (lo := (500382483 / 1000000000)) (hi := (125095621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206169 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206169 / 125000) = 1/(125000 / 206169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15552 : Bounds (500382483 / 1000000000) (125095621 / 250000000) (Real.log (206169 / 125000)) := by
  have h := reflection_log_15552_neg
  have he : Real.log (206169 / 125000) = -Real.log (125000 / 206169) := by
    rw [show ((206169 / 125000) : ℝ) = ((125000 / 206169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15553_neg : (1047972407 / 1000000000) ≤ -Real.log (43831 / 125000) ∧
    -Real.log (43831 / 125000) ≤ (1047972409 / 1000000000) := by
  have h := checkLog_sound (w := (18669 / 106331)) (n := 12)
    (lo := (354825227 / 1000000000)) (hi := (88706307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43831) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 43831) = 1/(43831 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15553 : Bounds (-1047972409 / 1000000000) (-1047972407 / 1000000000) (Real.log (43831 / 125000)) := by
  have h := reflection_log_15553_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15554_neg : (500958907 / 1000000000) ≤ -Real.log (1000000 / 1650303) ∧
    -Real.log (1000000 / 1650303) ≤ (125239727 / 250000000) := by
  have h := checkLog_sound (w := (650303 / 2650303)) (n := 12)
    (lo := (500958907 / 1000000000)) (hi := (125239727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650303 / 1000000) = 1/(1000000 / 1650303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15554 : Bounds (500958907 / 1000000000) (125239727 / 250000000) (Real.log (1650303 / 1000000)) := by
  have h := reflection_log_15554_neg
  have he : Real.log (1650303 / 1000000) = -Real.log (1000000 / 1650303) := by
    rw [show ((1650303 / 1000000) : ℝ) = ((1000000 / 1650303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15555_neg : (1050688213 / 1000000000) ≤ -Real.log (349697 / 1000000) ∧
    -Real.log (349697 / 1000000) ≤ (210137643 / 200000000) := by
  have h := checkLog_sound (w := (150303 / 849697)) (n := 12)
    (lo := (357541033 / 1000000000)) (hi := (178770517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349697) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349697) = 1/(349697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15555 : Bounds (-210137643 / 200000000) (-1050688213 / 1000000000) (Real.log (349697 / 1000000)) := by
  have h := reflection_log_15555_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15556_neg : (274864653 / 500000000) ≤ -Real.log (577106008191 / 1000000000000) ∧
    -Real.log (577106008191 / 1000000000000) ≤ (549729307 / 1000000000) := by
  have h := checkLog_sound (w := (422893991809 / 1577106008191)) (n := 12)
    (lo := (274864653 / 500000000)) (hi := (549729307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577106008191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577106008191) = 1/(577106008191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15556 : Bounds (-549729307 / 1000000000) (-274864653 / 500000000) (Real.log (577106008191 / 1000000000000)) := by
  have h := reflection_log_15556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15557_neg : (136897481 / 250000000) ≤ -Real.log (9036593439 / 15625000000) ∧
    -Real.log (9036593439 / 15625000000) ≤ (21903597 / 40000000) := by
  have h := checkLog_sound (w := (6588406561 / 24661593439)) (n := 12)
    (lo := (136897481 / 250000000)) (hi := (21903597 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 9036593439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 9036593439) = 1/(9036593439 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15557 : Bounds (-21903597 / 40000000) (-136897481 / 250000000) (Real.log (9036593439 / 15625000000)) := by
  have h := reflection_log_15557_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15558_neg : (154835489 / 100000000) ≤ -Real.log (100000000000 / 470372567361) ∧
    -Real.log (100000000000 / 470372567361) ≤ (1548354893 / 1000000000) := by
  have h := checkLog_sound (w := (70372567361 / 870372567361)) (n := 12)
    (lo := (16206053 / 100000000)) (hi := (162060531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470372567361 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(470372567361 / 400000000000) = 1/(100000000000 / 470372567361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15558 : Bounds (154835489 / 100000000) (1548354893 / 1000000000) (Real.log (470372567361 / 100000000000)) := by
  have h := reflection_log_15558_neg
  have he : Real.log (470372567361 / 100000000000) = -Real.log (100000000000 / 470372567361) := by
    rw [show ((470372567361 / 100000000000) : ℝ) = ((100000000000 / 470372567361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15559_neg : (19395589 / 12500000) ≤ -Real.log (62500000000 / 294952308713) ∧
    -Real.log (62500000000 / 294952308713) ≤ (1551647123 / 1000000000) := by
  have h := checkLog_sound (w := (44952308713 / 544952308713)) (n := 12)
    (lo := (4133819 / 25000000)) (hi := (165352761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294952308713 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(294952308713 / 250000000000) = 1/(62500000000 / 294952308713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15559 : Bounds (19395589 / 12500000) (1551647123 / 1000000000) (Real.log (294952308713 / 62500000000)) := by
  have h := reflection_log_15559_neg
  have he : Real.log (294952308713 / 62500000000) = -Real.log (62500000000 / 294952308713) := by
    rw [show ((294952308713 / 62500000000) : ℝ) = ((62500000000 / 294952308713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15560_neg : (1507470913 / 250000000) ≤ -Real.log (250000000000 / 103916666666667) ∧
    -Real.log (250000000000 / 103916666666667) ≤ (6029883661 / 1000000000) := by
  have h := checkLog_sound (w := (39916666666667 / 167916666666667)) (n := 12)
    (lo := (121176553 / 250000000)) (hi := (484706213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103916666666667 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(103916666666667 / 64000000000000) = 1/(250000000000 / 103916666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15560 : Bounds (1507470913 / 250000000) (6029883661 / 1000000000) (Real.log (103916666666667 / 250000000000)) := by
  have h := reflection_log_15560_neg
  have he : Real.log (103916666666667 / 250000000000) = -Real.log (250000000000 / 103916666666667) := by
    rw [show ((103916666666667 / 250000000000) : ℝ) = ((250000000000 / 103916666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15561_neg : (690844531 / 1000000000) ≤ -Real.log (5000 / 9977) ∧
    -Real.log (5000 / 9977) ≤ (172711133 / 250000000) := by
  have h := checkLog_sound (w := (4977 / 14977)) (n := 12)
    (lo := (690844531 / 1000000000)) (hi := (172711133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9977 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9977 / 5000) = 1/(5000 / 9977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15561 : Bounds (690844531 / 1000000000) (172711133 / 250000000) (Real.log (9977 / 5000)) := by
  have h := reflection_log_15561_neg
  have he : Real.log (9977 / 5000) = -Real.log (5000 / 9977) := by
    rw [show ((9977 / 5000) : ℝ) = ((5000 / 9977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15562_neg : (5381698971 / 1000000000) ≤ -Real.log (23 / 5000) ∧
    -Real.log (23 / 5000) ≤ (5381698979 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 993)) (n := 12)
    (lo := (529668711 / 1000000000)) (hi := (66208589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 368) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 368) = 1/(23 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15562 : Bounds (-5381698979 / 1000000000) (-5381698971 / 1000000000) (Real.log (23 / 5000)) := by
  have h := reflection_log_15562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15563_neg : (124363 / 125000000) ≤ -Real.log (5000000 / 5004977) ∧
    -Real.log (5000000 / 5004977) ≤ (198981 / 200000000) := by
  have h := checkLog_sound (w := (4977 / 10004977)) (n := 12)
    (lo := (124363 / 125000000)) (hi := (198981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004977 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004977 / 5000000) = 1/(5000000 / 5004977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15563 : Bounds (124363 / 125000000) (198981 / 200000000) (Real.log (5004977 / 5000000)) := by
  have h := reflection_log_15563_neg
  have he : Real.log (5004977 / 5000000) = -Real.log (5000000 / 5004977) := by
    rw [show ((5004977 / 5000000) : ℝ) = ((5000000 / 5004977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15564_neg : (199179 / 200000000) ≤ -Real.log (4995023 / 5000000) ∧
    -Real.log (4995023 / 5000000) ≤ (124487 / 125000000) := by
  have h := checkLog_sound (w := (4977 / 9995023)) (n := 12)
    (lo := (199179 / 200000000)) (hi := (124487 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995023) = 1/(4995023 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15564 : Bounds (-124487 / 125000000) (-199179 / 200000000) (Real.log (4995023 / 5000000)) := by
  have h := reflection_log_15564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15565_neg : (500580723 / 1000000000) ≤ -Real.log (1000000 / 1649679) ∧
    -Real.log (1000000 / 1649679) ≤ (125145181 / 250000000) := by
  have h := checkLog_sound (w := (649679 / 2649679)) (n := 12)
    (lo := (500580723 / 1000000000)) (hi := (125145181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1649679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1649679 / 1000000) = 1/(1000000 / 1649679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15565 : Bounds (500580723 / 1000000000) (125145181 / 250000000) (Real.log (1649679 / 1000000)) := by
  have h := reflection_log_15565_neg
  have he : Real.log (1649679 / 1000000) = -Real.log (1000000 / 1649679) := by
    rw [show ((1649679 / 1000000) : ℝ) = ((1000000 / 1649679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15566_neg : (1048905401 / 1000000000) ≤ -Real.log (350321 / 1000000) ∧
    -Real.log (350321 / 1000000) ≤ (1048905403 / 1000000000) := by
  have h := checkLog_sound (w := (149679 / 850321)) (n := 12)
    (lo := (355758221 / 1000000000)) (hi := (177879111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350321) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 350321) = 1/(350321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15566 : Bounds (-1048905403 / 1000000000) (-1048905401 / 1000000000) (Real.log (350321 / 1000000)) := by
  have h := reflection_log_15566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15567_neg : (501157639 / 1000000000) ≤ -Real.log (1000000 / 1650631) ∧
    -Real.log (1000000 / 1650631) ≤ (12528941 / 25000000) := by
  have h := checkLog_sound (w := (650631 / 2650631)) (n := 12)
    (lo := (501157639 / 1000000000)) (hi := (12528941 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650631 / 1000000) = 1/(1000000 / 1650631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15567 : Bounds (501157639 / 1000000000) (12528941 / 25000000) (Real.log (1650631 / 1000000)) := by
  have h := reflection_log_15567_neg
  have he : Real.log (1650631 / 1000000) = -Real.log (1000000 / 1650631) := by
    rw [show ((1650631 / 1000000) : ℝ) = ((1000000 / 1650631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15568_neg : (65726663 / 62500000) ≤ -Real.log (349369 / 1000000) ∧
    -Real.log (349369 / 1000000) ≤ (105162661 / 100000000) := by
  have h := checkLog_sound (w := (150631 / 849369)) (n := 12)
    (lo := (89619857 / 250000000)) (hi := (358479429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349369) = 1/(349369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15568 : Bounds (-105162661 / 100000000) (-65726663 / 62500000) (Real.log (349369 / 1000000)) := by
  have h := reflection_log_15568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15569_neg : (550468969 / 1000000000) ≤ -Real.log (576679301839 / 1000000000000) ∧
    -Real.log (576679301839 / 1000000000000) ≤ (55046897 / 100000000) := by
  have h := checkLog_sound (w := (423320698161 / 1576679301839)) (n := 12)
    (lo := (550468969 / 1000000000)) (hi := (55046897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 576679301839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 576679301839) = 1/(576679301839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15569 : Bounds (-55046897 / 100000000) (-550468969 / 1000000000) (Real.log (576679301839 / 1000000000000)) := by
  have h := reflection_log_15569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15570_neg : (274162339 / 500000000) ≤ -Real.log (577917196959 / 1000000000000) ∧
    -Real.log (577917196959 / 1000000000000) ≤ (548324679 / 1000000000) := by
  have h := checkLog_sound (w := (422082803041 / 1577917196959)) (n := 12)
    (lo := (274162339 / 500000000)) (hi := (548324679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577917196959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577917196959) = 1/(577917196959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15570 : Bounds (-548324679 / 1000000000) (-274162339 / 500000000) (Real.log (577917196959 / 1000000000000)) := by
  have h := reflection_log_15570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15571_neg : (387371531 / 250000000) ≤ -Real.log (250000000000 / 1177262425033) ∧
    -Real.log (250000000000 / 1177262425033) ≤ (1549486127 / 1000000000) := by
  have h := checkLog_sound (w := (177262425033 / 2177262425033)) (n := 12)
    (lo := (40797941 / 250000000)) (hi := (32638353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177262425033 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1177262425033 / 1000000000000) = 1/(250000000000 / 1177262425033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15571 : Bounds (387371531 / 250000000) (1549486127 / 1000000000) (Real.log (1177262425033 / 250000000000)) := by
  have h := reflection_log_15571_neg
  have he : Real.log (1177262425033 / 250000000000) = -Real.log (250000000000 / 1177262425033) := by
    rw [show ((1177262425033 / 250000000000) : ℝ) = ((250000000000 / 1177262425033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15572_neg : (776392123 / 500000000) ≤ -Real.log (250000000000 / 1181151590439) ∧
    -Real.log (250000000000 / 1181151590439) ≤ (1552784249 / 1000000000) := by
  have h := checkLog_sound (w := (181151590439 / 2181151590439)) (n := 12)
    (lo := (83244943 / 500000000)) (hi := (166489887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181151590439 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1181151590439 / 1000000000000) = 1/(250000000000 / 1181151590439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15572 : Bounds (776392123 / 500000000) (1552784249 / 1000000000) (Real.log (1181151590439 / 250000000000)) := by
  have h := reflection_log_15572_neg
  have he : Real.log (1181151590439 / 250000000000) = -Real.log (250000000000 / 1181151590439) := by
    rw [show ((1181151590439 / 250000000000) : ℝ) = ((250000000000 / 1181151590439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15573_neg : (1507470913 / 250000000) ≤ -Real.log (500000000000 / 207833333333333) ∧
    -Real.log (500000000000 / 207833333333333) ≤ (6029883661 / 1000000000) := by
  have h := checkLog_sound (w := (79833333333333 / 335833333333333)) (n := 12)
    (lo := (121176553 / 250000000)) (hi := (484706213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207833333333333 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(207833333333333 / 128000000000000) = 1/(500000000000 / 207833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15573 : Bounds (1507470913 / 250000000) (6029883661 / 1000000000) (Real.log (207833333333333 / 500000000000)) := by
  have h := reflection_log_15573_neg
  have he : Real.log (207833333333333 / 500000000000) = -Real.log (500000000000 / 207833333333333) := by
    rw [show ((207833333333333 / 500000000000) : ℝ) = ((500000000000 / 207833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15574_neg : (3036271751 / 500000000) ≤ -Real.log (500000000000 / 216891304347827) ∧
    -Real.log (500000000000 / 216891304347827) ≤ (6072543511 / 1000000000) := by
  have h := checkLog_sound (w := (88891304347827 / 344891304347827)) (n := 12)
    (lo := (263683031 / 500000000)) (hi := (527366063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216891304347827 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(216891304347827 / 128000000000000) = 1/(500000000000 / 216891304347827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15574 : Bounds (3036271751 / 500000000) (6072543511 / 1000000000) (Real.log (216891304347827 / 500000000000)) := by
  have h := reflection_log_15574_neg
  have he : Real.log (216891304347827 / 500000000000) = -Real.log (500000000000 / 216891304347827) := by
    rw [show ((216891304347827 / 500000000000) : ℝ) = ((500000000000 / 216891304347827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15575_neg : (690944757 / 1000000000) ≤ -Real.log (2500 / 4989) ∧
    -Real.log (2500 / 4989) ≤ (345472379 / 500000000) := by
  have h := checkLog_sound (w := (2489 / 7489)) (n := 12)
    (lo := (690944757 / 1000000000)) (hi := (345472379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4989 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4989 / 2500) = 1/(2500 / 4989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15575 : Bounds (690944757 / 1000000000) (345472379 / 500000000) (Real.log (4989 / 2500)) := by
  have h := reflection_log_15575_neg
  have he : Real.log (4989 / 2500) = -Real.log (2500 / 4989) := by
    rw [show ((4989 / 2500) : ℝ) = ((2500 / 4989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15576_neg : (2713075367 / 500000000) ≤ -Real.log (11 / 2500) ∧
    -Real.log (11 / 2500) ≤ (2713075371 / 500000000) := by
  have h := checkLog_sound (w := (273 / 977)) (n := 12)
    (lo := (287060237 / 500000000)) (hi := (22964819 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 352) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 352) = 1/(11 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15576 : Bounds (-2713075371 / 500000000) (-2713075367 / 500000000) (Real.log (11 / 2500)) := by
  have h := reflection_log_15576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15577_neg : (31097 / 31250000) ≤ -Real.log (2500000 / 2502489) ∧
    -Real.log (2500000 / 2502489) ≤ (199021 / 200000000) := by
  have h := checkLog_sound (w := (2489 / 5002489)) (n := 12)
    (lo := (31097 / 31250000)) (hi := (199021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502489 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502489 / 2500000) = 1/(2500000 / 2502489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15577 : Bounds (31097 / 31250000) (199021 / 200000000) (Real.log (2502489 / 2500000)) := by
  have h := reflection_log_15577_neg
  have he : Real.log (2502489 / 2500000) = -Real.log (2500000 / 2502489) := by
    rw [show ((2502489 / 2500000) : ℝ) = ((2500000 / 2502489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15578_neg : (199219 / 200000000) ≤ -Real.log (2497511 / 2500000) ∧
    -Real.log (2497511 / 2500000) ≤ (3891 / 3906250) := by
  have h := checkLog_sound (w := (2489 / 4997511)) (n := 12)
    (lo := (199219 / 200000000)) (hi := (3891 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497511) = 1/(2497511 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15578 : Bounds (-3891 / 3906250) (-199219 / 200000000) (Real.log (2497511 / 2500000)) := by
  have h := reflection_log_15578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15579_neg : (50077953 / 100000000) ≤ -Real.log (1000000 / 1650007) ∧
    -Real.log (1000000 / 1650007) ≤ (500779531 / 1000000000) := by
  have h := checkLog_sound (w := (650007 / 2650007)) (n := 12)
    (lo := (50077953 / 100000000)) (hi := (500779531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650007 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650007 / 1000000) = 1/(1000000 / 1650007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15579 : Bounds (50077953 / 100000000) (500779531 / 1000000000) (Real.log (1650007 / 1000000)) := by
  have h := reflection_log_15579_neg
  have he : Real.log (1650007 / 1000000) = -Real.log (1000000 / 1650007) := by
    rw [show ((1650007 / 1000000) : ℝ) = ((1000000 / 1650007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15580_neg : (262460531 / 250000000) ≤ -Real.log (349993 / 1000000) ∧
    -Real.log (349993 / 1000000) ≤ (524921063 / 500000000) := by
  have h := checkLog_sound (w := (150007 / 849993)) (n := 12)
    (lo := (11146717 / 31250000)) (hi := (71338989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349993) = 1/(349993 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15580 : Bounds (-524921063 / 500000000) (-262460531 / 250000000) (Real.log (349993 / 1000000)) := by
  have h := reflection_log_15580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15581_neg : (250678771 / 500000000) ≤ -Real.log (1000000 / 1650961) ∧
    -Real.log (1000000 / 1650961) ≤ (501357543 / 1000000000) := by
  have h := checkLog_sound (w := (650961 / 2650961)) (n := 12)
    (lo := (250678771 / 500000000)) (hi := (501357543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650961 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650961 / 1000000) = 1/(1000000 / 1650961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15581 : Bounds (250678771 / 500000000) (501357543 / 1000000000) (Real.log (1650961 / 1000000)) := by
  have h := reflection_log_15581_neg
  have he : Real.log (1650961 / 1000000) = -Real.log (1000000 / 1650961) := by
    rw [show ((1650961 / 1000000) : ℝ) = ((1000000 / 1650961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15582_neg : (526285807 / 500000000) ≤ -Real.log (349039 / 1000000) ∧
    -Real.log (349039 / 1000000) ≤ (32892863 / 31250000) := by
  have h := checkLog_sound (w := (150961 / 849039)) (n := 12)
    (lo := (179712217 / 500000000)) (hi := (71884887 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349039) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349039) = 1/(349039 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15582 : Bounds (-32892863 / 31250000) (-526285807 / 500000000) (Real.log (349039 / 1000000)) := by
  have h := reflection_log_15582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15583_neg : (68901759 / 125000000) ≤ -Real.log (576249776479 / 1000000000000) ∧
    -Real.log (576249776479 / 1000000000000) ≤ (551214073 / 1000000000) := by
  have h := checkLog_sound (w := (423750223521 / 1576249776479)) (n := 12)
    (lo := (68901759 / 125000000)) (hi := (551214073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 576249776479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 576249776479) = 1/(576249776479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15583 : Bounds (-551214073 / 1000000000) (-68901759 / 125000000) (Real.log (576249776479 / 1000000000000)) := by
  have h := reflection_log_15583_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15584_neg : (274531297 / 500000000) ≤ -Real.log (577490899951 / 1000000000000) ∧
    -Real.log (577490899951 / 1000000000000) ≤ (109812519 / 200000000) := by
  have h := checkLog_sound (w := (422509100049 / 1577490899951)) (n := 12)
    (lo := (274531297 / 500000000)) (hi := (109812519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577490899951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577490899951) = 1/(577490899951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15584 : Bounds (-109812519 / 200000000) (-274531297 / 500000000) (Real.log (577490899951 / 1000000000000)) := by
  have h := reflection_log_15584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15585_neg : (1550621653 / 1000000000) ≤ -Real.log (250000000000 / 1178600000571) ∧
    -Real.log (250000000000 / 1178600000571) ≤ (193827707 / 125000000) := by
  have h := checkLog_sound (w := (178600000571 / 2178600000571)) (n := 12)
    (lo := (164327293 / 1000000000)) (hi := (82163647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178600000571 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1178600000571 / 1000000000000) = 1/(250000000000 / 1178600000571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15585 : Bounds (1550621653 / 1000000000) (193827707 / 125000000) (Real.log (1178600000571 / 250000000000)) := by
  have h := reflection_log_15585_neg
  have he : Real.log (1178600000571 / 250000000000) = -Real.log (250000000000 / 1178600000571) := by
    rw [show ((1178600000571 / 250000000000) : ℝ) = ((250000000000 / 1178600000571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15586_neg : (388482289 / 250000000) ≤ -Real.log (31250000000 / 147813084641) ∧
    -Real.log (31250000000 / 147813084641) ≤ (1553929159 / 1000000000) := by
  have h := checkLog_sound (w := (22813084641 / 272813084641)) (n := 12)
    (lo := (41908699 / 250000000)) (hi := (167634797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147813084641 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(147813084641 / 125000000000) = 1/(31250000000 / 147813084641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15586 : Bounds (388482289 / 250000000) (1553929159 / 1000000000) (Real.log (147813084641 / 31250000000)) := by
  have h := reflection_log_15586_neg
  have he : Real.log (147813084641 / 31250000000) = -Real.log (31250000000 / 147813084641) := by
    rw [show ((147813084641 / 31250000000) : ℝ) = ((31250000000 / 147813084641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15587_neg : (3036271751 / 500000000) ≤ -Real.log (250000000000 / 108445652173913) ∧
    -Real.log (250000000000 / 108445652173913) ≤ (6072543511 / 1000000000) := by
  have h := checkLog_sound (w := (44445652173913 / 172445652173913)) (n := 12)
    (lo := (263683031 / 500000000)) (hi := (527366063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108445652173913 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(108445652173913 / 64000000000000) = 1/(250000000000 / 108445652173913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15587 : Bounds (3036271751 / 500000000) (6072543511 / 1000000000) (Real.log (108445652173913 / 250000000000)) := by
  have h := reflection_log_15587_neg
  have he : Real.log (108445652173913 / 250000000000) = -Real.log (250000000000 / 108445652173913) := by
    rw [show ((108445652173913 / 250000000000) : ℝ) = ((250000000000 / 108445652173913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15588_neg : (611709549 / 100000000) ≤ -Real.log (62500000000 / 28346590909091) ∧
    -Real.log (62500000000 / 28346590909091) ≤ (6117095499 / 1000000000) := by
  have h := checkLog_sound (w := (12346590909091 / 44346590909091)) (n := 12)
    (lo := (11438361 / 20000000)) (hi := (571918051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28346590909091 / 16000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(28346590909091 / 16000000000000) = 1/(62500000000 / 28346590909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15588 : Bounds (611709549 / 100000000) (6117095499 / 1000000000) (Real.log (28346590909091 / 62500000000)) := by
  have h := reflection_log_15588_neg
  have he : Real.log (28346590909091 / 62500000000) = -Real.log (62500000000 / 28346590909091) := by
    rw [show ((28346590909091 / 62500000000) : ℝ) = ((62500000000 / 28346590909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15589_neg : (172761243 / 250000000) ≤ -Real.log (5000 / 9979) ∧
    -Real.log (5000 / 9979) ≤ (691044973 / 1000000000) := by
  have h := checkLog_sound (w := (4979 / 14979)) (n := 12)
    (lo := (172761243 / 250000000)) (hi := (691044973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9979 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9979 / 5000) = 1/(5000 / 9979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15589 : Bounds (172761243 / 250000000) (691044973 / 1000000000) (Real.log (9979 / 5000)) := by
  have h := reflection_log_15589_neg
  have he : Real.log (9979 / 5000) = -Real.log (5000 / 9979) := by
    rw [show ((9979 / 5000) : ℝ) = ((5000 / 9979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15590_neg : (5472670749 / 1000000000) ≤ -Real.log (21 / 5000) ∧
    -Real.log (21 / 5000) ≤ (5472670757 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 961)) (n := 12)
    (lo := (620640489 / 1000000000)) (hi := (62064049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 336) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 336) = 1/(21 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15590 : Bounds (-5472670757 / 1000000000) (-5472670749 / 1000000000) (Real.log (21 / 5000)) := by
  have h := reflection_log_15590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15591_neg : (124413 / 125000000) ≤ -Real.log (5000000 / 5004979) ∧
    -Real.log (5000000 / 5004979) ≤ (199061 / 200000000) := by
  have h := checkLog_sound (w := (4979 / 10004979)) (n := 12)
    (lo := (124413 / 125000000)) (hi := (199061 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004979 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004979 / 5000000) = 1/(5000000 / 5004979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15591 : Bounds (124413 / 125000000) (199061 / 200000000) (Real.log (5004979 / 5000000)) := by
  have h := reflection_log_15591_neg
  have he : Real.log (5004979 / 5000000) = -Real.log (5000000 / 5004979) := by
    rw [show ((5004979 / 5000000) : ℝ) = ((5000000 / 5004979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15592_neg : (124537 / 125000000) ≤ -Real.log (4995021 / 5000000) ∧
    -Real.log (4995021 / 5000000) ≤ (996297 / 1000000000) := by
  have h := checkLog_sound (w := (4979 / 9995021)) (n := 12)
    (lo := (124537 / 125000000)) (hi := (996297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995021) = 1/(4995021 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15592 : Bounds (-996297 / 1000000000) (-124537 / 125000000) (Real.log (4995021 / 5000000)) := by
  have h := reflection_log_15592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15593_neg : (500979509 / 1000000000) ≤ -Real.log (1000000 / 1650337) ∧
    -Real.log (1000000 / 1650337) ≤ (50097951 / 100000000) := by
  have h := checkLog_sound (w := (650337 / 2650337)) (n := 12)
    (lo := (500979509 / 1000000000)) (hi := (50097951 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650337 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650337 / 1000000) = 1/(1000000 / 1650337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15593 : Bounds (500979509 / 1000000000) (50097951 / 100000000) (Real.log (1650337 / 1000000)) := by
  have h := reflection_log_15593_neg
  have he : Real.log (1650337 / 1000000) = -Real.log (1000000 / 1650337) := by
    rw [show ((1650337 / 1000000) : ℝ) = ((1000000 / 1650337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15594_neg : (262696361 / 250000000) ≤ -Real.log (349663 / 1000000) ∧
    -Real.log (349663 / 1000000) ≤ (525392723 / 500000000) := by
  have h := checkLog_sound (w := (150337 / 849663)) (n := 12)
    (lo := (44704783 / 125000000)) (hi := (71527653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349663) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349663) = 1/(349663 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15594 : Bounds (-525392723 / 500000000) (-262696361 / 250000000) (Real.log (349663 / 1000000)) := by
  have h := reflection_log_15594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15595_neg : (501558617 / 1000000000) ≤ -Real.log (1000000 / 1651293) ∧
    -Real.log (1000000 / 1651293) ≤ (250779309 / 500000000) := by
  have h := checkLog_sound (w := (651293 / 2651293)) (n := 12)
    (lo := (501558617 / 1000000000)) (hi := (250779309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651293 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651293 / 1000000) = 1/(1000000 / 1651293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15595 : Bounds (501558617 / 1000000000) (250779309 / 500000000) (Real.log (1651293 / 1000000)) := by
  have h := reflection_log_15595_neg
  have he : Real.log (1651293 / 1000000) = -Real.log (1000000 / 1651293) := by
    rw [show ((1651293 / 1000000) : ℝ) = ((1000000 / 1651293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15596_neg : (4214093 / 4000000) ≤ -Real.log (348707 / 1000000) ∧
    -Real.log (348707 / 1000000) ≤ (263380813 / 250000000) := by
  have h := checkLog_sound (w := (151293 / 848707)) (n := 12)
    (lo := (36037607 / 100000000)) (hi := (360376071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348707) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 348707) = 1/(348707 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15596 : Bounds (-263380813 / 250000000) (-4214093 / 4000000) (Real.log (348707 / 1000000)) := by
  have h := reflection_log_15596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15597_neg : (551964633 / 1000000000) ≤ -Real.log (575817428151 / 1000000000000) ∧
    -Real.log (575817428151 / 1000000000000) ≤ (275982317 / 500000000) := by
  have h := checkLog_sound (w := (424182571849 / 1575817428151)) (n := 12)
    (lo := (551964633 / 1000000000)) (hi := (275982317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 575817428151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 575817428151) = 1/(575817428151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15597 : Bounds (-275982317 / 500000000) (-551964633 / 1000000000) (Real.log (575817428151 / 1000000000000)) := by
  have h := reflection_log_15597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15598_neg : (34362871 / 62500000) ≤ -Real.log (577061786431 / 1000000000000) ∧
    -Real.log (577061786431 / 1000000000000) ≤ (549805937 / 1000000000) := by
  have h := checkLog_sound (w := (422938213569 / 1577061786431)) (n := 12)
    (lo := (34362871 / 62500000)) (hi := (549805937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577061786431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577061786431) = 1/(577061786431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15598 : Bounds (-549805937 / 1000000000) (-34362871 / 62500000) (Real.log (577061786431 / 1000000000000)) := by
  have h := reflection_log_15598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15599_neg : (1551764953 / 1000000000) ≤ -Real.log (500000000000 / 2359896528943) ∧
    -Real.log (500000000000 / 2359896528943) ≤ (387941239 / 250000000) := by
  have h := checkLog_sound (w := (359896528943 / 4359896528943)) (n := 12)
    (lo := (165470593 / 1000000000)) (hi := (82735297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2359896528943 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2359896528943 / 2000000000000) = 1/(500000000000 / 2359896528943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15599 : Bounds (1551764953 / 1000000000) (387941239 / 250000000) (Real.log (2359896528943 / 500000000000)) := by
  have h := reflection_log_15599_neg
  have he : Real.log (2359896528943 / 500000000000) = -Real.log (500000000000 / 2359896528943) := by
    rw [show ((2359896528943 / 500000000000) : ℝ) = ((500000000000 / 2359896528943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15600_neg : (1555081867 / 1000000000) ≤ -Real.log (250000000000 / 1183868548667) ∧
    -Real.log (250000000000 / 1183868548667) ≤ (155508187 / 100000000) := by
  have h := checkLog_sound (w := (183868548667 / 2183868548667)) (n := 12)
    (lo := (168787507 / 1000000000)) (hi := (42196877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183868548667 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1183868548667 / 1000000000000) = 1/(250000000000 / 1183868548667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15600 : Bounds (1555081867 / 1000000000) (155508187 / 100000000) (Real.log (1183868548667 / 250000000000)) := by
  have h := reflection_log_15600_neg
  have he : Real.log (1183868548667 / 250000000000) = -Real.log (250000000000 / 1183868548667) := by
    rw [show ((1183868548667 / 250000000000) : ℝ) = ((250000000000 / 1183868548667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15601_neg : (611709549 / 100000000) ≤ -Real.log (500000000000 / 226772727272727) ∧
    -Real.log (500000000000 / 226772727272727) ≤ (6117095499 / 1000000000) := by
  have h := checkLog_sound (w := (98772727272727 / 354772727272727)) (n := 12)
    (lo := (11438361 / 20000000)) (hi := (571918051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226772727272727 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(226772727272727 / 128000000000000) = 1/(500000000000 / 226772727272727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15601 : Bounds (611709549 / 100000000) (6117095499 / 1000000000) (Real.log (226772727272727 / 500000000000)) := by
  have h := reflection_log_15601_neg
  have he : Real.log (226772727272727 / 500000000000) = -Real.log (500000000000 / 226772727272727) := by
    rw [show ((226772727272727 / 500000000000) : ℝ) = ((500000000000 / 226772727272727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15602_neg : (6163715721 / 1000000000) ≤ -Real.log (500000000000 / 237595238095239) ∧
    -Real.log (500000000000 / 237595238095239) ≤ (616371573 / 100000000) := by
  have h := checkLog_sound (w := (109595238095239 / 365595238095239)) (n := 12)
    (lo := (618538281 / 1000000000)) (hi := (309269141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237595238095239 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(237595238095239 / 128000000000000) = 1/(500000000000 / 237595238095239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15602 : Bounds (6163715721 / 1000000000) (616371573 / 100000000) (Real.log (237595238095239 / 500000000000)) := by
  have h := reflection_log_15602_neg
  have he : Real.log (237595238095239 / 500000000000) = -Real.log (500000000000 / 237595238095239) := by
    rw [show ((237595238095239 / 500000000000) : ℝ) = ((500000000000 / 237595238095239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15603_neg : (691145177 / 1000000000) ≤ -Real.log (250 / 499) ∧
    -Real.log (250 / 499) ≤ (345572589 / 500000000) := by
  have h := checkLog_sound (w := (249 / 749)) (n := 12)
    (lo := (691145177 / 1000000000)) (hi := (345572589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 250) = 1/(250 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15603 : Bounds (691145177 / 1000000000) (345572589 / 500000000) (Real.log (499 / 250)) := by
  have h := reflection_log_15603_neg
  have he : Real.log (499 / 250) = -Real.log (250 / 499) := by
    rw [show ((499 / 250) : ℝ) = ((250 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15604_neg : (5521460913 / 1000000000) ≤ -Real.log (1 / 250) ∧
    -Real.log (1 / 250) ≤ (5521460921 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(125 / 64) = 1/(1 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15604 : Bounds (-5521460921 / 1000000000) (-5521460913 / 1000000000) (Real.log (1 / 250)) := by
  have h := reflection_log_15604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15605_neg : (62219 / 62500000) ≤ -Real.log (250000 / 250249) ∧
    -Real.log (250000 / 250249) ≤ (199101 / 200000000) := by
  have h := checkLog_sound (w := (249 / 500249)) (n := 12)
    (lo := (62219 / 62500000)) (hi := (199101 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250249 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250249 / 250000) = 1/(250000 / 250249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15605 : Bounds (62219 / 62500000) (199101 / 200000000) (Real.log (250249 / 250000)) := by
  have h := reflection_log_15605_neg
  have he : Real.log (250249 / 250000) = -Real.log (250000 / 250249) := by
    rw [show ((250249 / 250000) : ℝ) = ((250000 / 250249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15606_neg : (62281 / 62500000) ≤ -Real.log (249751 / 250000) ∧
    -Real.log (249751 / 250000) ≤ (996497 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 499751)) (n := 12)
    (lo := (62281 / 62500000)) (hi := (996497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249751) = 1/(249751 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15606 : Bounds (-996497 / 1000000000) (-62281 / 62500000) (Real.log (249751 / 250000)) := by
  have h := reflection_log_15606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15607_neg : (25059033 / 50000000) ≤ -Real.log (1000000 / 1650669) ∧
    -Real.log (1000000 / 1650669) ≤ (501180661 / 1000000000) := by
  have h := checkLog_sound (w := (650669 / 2650669)) (n := 12)
    (lo := (25059033 / 50000000)) (hi := (501180661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650669 / 1000000) = 1/(1000000 / 1650669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15607 : Bounds (25059033 / 50000000) (501180661 / 1000000000) (Real.log (1650669 / 1000000)) := by
  have h := reflection_log_15607_neg
  have he : Real.log (1650669 / 1000000) = -Real.log (1000000 / 1650669) := by
    rw [show ((1650669 / 1000000) : ℝ) = ((1000000 / 1650669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15608_neg : (1051735381 / 1000000000) ≤ -Real.log (349331 / 1000000) ∧
    -Real.log (349331 / 1000000) ≤ (1051735383 / 1000000000) := by
  have h := checkLog_sound (w := (150669 / 849331)) (n := 12)
    (lo := (358588201 / 1000000000)) (hi := (179294101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349331) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349331) = 1/(349331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15608 : Bounds (-1051735383 / 1000000000) (-1051735381 / 1000000000) (Real.log (349331 / 1000000)) := by
  have h := reflection_log_15608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15609_neg : (250880431 / 500000000) ≤ -Real.log (1000000 / 1651627) ∧
    -Real.log (1000000 / 1651627) ≤ (501760863 / 1000000000) := by
  have h := checkLog_sound (w := (651627 / 2651627)) (n := 12)
    (lo := (250880431 / 500000000)) (hi := (501760863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651627 / 1000000) = 1/(1000000 / 1651627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15609 : Bounds (250880431 / 500000000) (501760863 / 1000000000) (Real.log (1651627 / 1000000)) := by
  have h := reflection_log_15609_neg
  have he : Real.log (1651627 / 1000000) = -Real.log (1000000 / 1651627) := by
    rw [show ((1651627 / 1000000) : ℝ) = ((1000000 / 1651627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15610_neg : (1054481533 / 1000000000) ≤ -Real.log (348373 / 1000000) ∧
    -Real.log (348373 / 1000000) ≤ (210896307 / 200000000) := by
  have h := checkLog_sound (w := (151627 / 848373)) (n := 12)
    (lo := (361334353 / 1000000000)) (hi := (180667177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348373) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 348373) = 1/(348373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15610 : Bounds (-210896307 / 200000000) (-1054481533 / 1000000000) (Real.log (348373 / 1000000)) := by
  have h := reflection_log_15610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15611_neg : (552720671 / 1000000000) ≤ -Real.log (575382252871 / 1000000000000) ∧
    -Real.log (575382252871 / 1000000000000) ≤ (17272521 / 31250000) := by
  have h := checkLog_sound (w := (424617747129 / 1575382252871)) (n := 12)
    (lo := (552720671 / 1000000000)) (hi := (17272521 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 575382252871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 575382252871) = 1/(575382252871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15611 : Bounds (-17272521 / 31250000) (-552720671 / 1000000000) (Real.log (575382252871 / 1000000000000)) := by
  have h := reflection_log_15611_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15612_neg : (550554721 / 1000000000) ≤ -Real.log (576629852439 / 1000000000000) ∧
    -Real.log (576629852439 / 1000000000000) ≤ (275277361 / 500000000) := by
  have h := checkLog_sound (w := (423370147561 / 1576629852439)) (n := 12)
    (lo := (550554721 / 1000000000)) (hi := (275277361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 576629852439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 576629852439) = 1/(576629852439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15612 : Bounds (-275277361 / 500000000) (-550554721 / 1000000000) (Real.log (576629852439 / 1000000000000)) := by
  have h := reflection_log_15612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15613_neg : (1552916041 / 1000000000) ≤ -Real.log (125000000000 / 590653635091) ∧
    -Real.log (125000000000 / 590653635091) ≤ (388229011 / 250000000) := by
  have h := checkLog_sound (w := (90653635091 / 1090653635091)) (n := 12)
    (lo := (166621681 / 1000000000)) (hi := (83310841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590653635091 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(590653635091 / 500000000000) = 1/(125000000000 / 590653635091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15613 : Bounds (1552916041 / 1000000000) (388229011 / 250000000) (Real.log (590653635091 / 125000000000)) := by
  have h := reflection_log_15613_neg
  have he : Real.log (590653635091 / 125000000000) = -Real.log (125000000000 / 590653635091) := by
    rw [show ((590653635091 / 125000000000) : ℝ) = ((125000000000 / 590653635091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15614_neg : (311248479 / 200000000) ≤ -Real.log (500000000000 / 2370486518761) ∧
    -Real.log (500000000000 / 2370486518761) ≤ (778121199 / 500000000) := by
  have h := checkLog_sound (w := (370486518761 / 4370486518761)) (n := 12)
    (lo := (33989607 / 200000000)) (hi := (42487009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2370486518761 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2370486518761 / 2000000000000) = 1/(500000000000 / 2370486518761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15614 : Bounds (311248479 / 200000000) (778121199 / 500000000) (Real.log (2370486518761 / 500000000000)) := by
  have h := reflection_log_15614_neg
  have he : Real.log (2370486518761 / 500000000000) = -Real.log (500000000000 / 2370486518761) := by
    rw [show ((2370486518761 / 500000000000) : ℝ) = ((500000000000 / 2370486518761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15615_neg : (6163715721 / 1000000000) ≤ -Real.log (250000000000 / 118797619047619) ∧
    -Real.log (250000000000 / 118797619047619) ≤ (616371573 / 100000000) := by
  have h := checkLog_sound (w := (54797619047619 / 182797619047619)) (n := 12)
    (lo := (618538281 / 1000000000)) (hi := (309269141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118797619047619 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(118797619047619 / 64000000000000) = 1/(250000000000 / 118797619047619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15615 : Bounds (6163715721 / 1000000000) (616371573 / 100000000) (Real.log (118797619047619 / 250000000000)) := by
  have h := reflection_log_15615_neg
  have he : Real.log (118797619047619 / 250000000000) = -Real.log (250000000000 / 118797619047619) := by
    rw [show ((118797619047619 / 250000000000) : ℝ) = ((250000000000 / 118797619047619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

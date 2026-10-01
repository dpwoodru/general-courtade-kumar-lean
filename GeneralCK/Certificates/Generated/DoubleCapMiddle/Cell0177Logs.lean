import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0177
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

theorem reflection_log_1_neg : (137971761 / 500000000) ≤ -Real.log (5120 / 6747) ∧
    -Real.log (5120 / 6747) ≤ (275943523 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 11867)) (n := 12)
    (lo := (137971761 / 500000000)) (hi := (275943523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6747 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6747 / 5120) = 1/(5120 / 6747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (137971761 / 500000000) (275943523 / 1000000000) (Real.log (6747 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6747 / 5120) = -Real.log (5120 / 6747) := by
    rw [show ((6747 / 5120) : ℝ) = ((5120 / 6747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (382393473 / 1000000000) ≤ -Real.log (3493 / 5120) ∧
    -Real.log (3493 / 5120) ≤ (191196737 / 500000000) := by
  have h := checkLog_sound (w := (1627 / 8613)) (n := 12)
    (lo := (382393473 / 1000000000)) (hi := (191196737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3493) = 1/(3493 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-191196737 / 500000000) (-382393473 / 1000000000) (Real.log (3493 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (275498781 / 1000000000) ≤ -Real.log (640 / 843) ∧
    -Real.log (640 / 843) ≤ (137749391 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1483)) (n := 12)
    (lo := (275498781 / 1000000000)) (hi := (137749391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843 / 640) = 1/(640 / 843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (275498781 / 1000000000) (137749391 / 500000000) (Real.log (843 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (843 / 640) = -Real.log (640 / 843) := by
    rw [show ((843 / 640) : ℝ) = ((640 / 843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (381534981 / 1000000000) ≤ -Real.log (437 / 640) ∧
    -Real.log (437 / 640) ≤ (190767491 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1077)) (n := 12)
    (lo := (381534981 / 1000000000)) (hi := (190767491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 437) = 1/(437 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-190767491 / 500000000) (-381534981 / 1000000000) (Real.log (437 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (122994307 / 250000000) ≤ -Real.log (2560 / 4187) ∧
    -Real.log (2560 / 4187) ≤ (491977229 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 6747)) (n := 12)
    (lo := (122994307 / 250000000)) (hi := (491977229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4187 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4187 / 2560) = 1/(2560 / 4187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (122994307 / 250000000) (491977229 / 1000000000) (Real.log (4187 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4187 / 2560) = -Real.log (2560 / 4187) := by
    rw [show ((4187 / 2560) : ℝ) = ((2560 / 4187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (126169667 / 125000000) ≤ -Real.log (933 / 2560) ∧
    -Real.log (933 / 2560) ≤ (504678669 / 500000000) := by
  have h := checkLog_sound (w := (347 / 2213)) (n := 12)
    (lo := (79052539 / 250000000)) (hi := (316210157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 933) = 1/(933 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-504678669 / 500000000) (-126169667 / 125000000) (Real.log (933 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122815117 / 250000000) ≤ -Real.log (320 / 523) ∧
    -Real.log (320 / 523) ≤ (491260469 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 843)) (n := 12)
    (lo := (122815117 / 250000000)) (hi := (491260469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((523 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(523 / 320) = 1/(320 / 523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122815117 / 250000000) (491260469 / 1000000000) (Real.log (523 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (523 / 320) = -Real.log (320 / 523) := by
    rw [show ((523 / 320) : ℝ) = ((320 / 523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50307353 / 50000000) ≤ -Real.log (117 / 320) ∧
    -Real.log (117 / 320) ≤ (503073531 / 500000000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 117) = 1/(117 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-503073531 / 500000000) (-50307353 / 50000000) (Real.log (117 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (376873571 / 1000000000) ≤ -Real.log (25000 / 36443) ∧
    -Real.log (25000 / 36443) ≤ (94218393 / 250000000) := by
  have h := checkLog_sound (w := (11443 / 61443)) (n := 12)
    (lo := (376873571 / 1000000000)) (hi := (94218393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36443 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36443 / 25000) = 1/(25000 / 36443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (376873571 / 1000000000) (94218393 / 250000000) (Real.log (36443 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (36443 / 25000) = -Real.log (25000 / 36443) := by
    rw [show ((36443 / 25000) : ℝ) = ((25000 / 36443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (122394561 / 200000000) ≤ -Real.log (13557 / 25000) ∧
    -Real.log (13557 / 25000) ≤ (305986403 / 500000000) := by
  have h := checkLog_sound (w := (11443 / 38557)) (n := 12)
    (lo := (122394561 / 200000000)) (hi := (305986403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 13557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 13557) = 1/(13557 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-305986403 / 500000000) (-122394561 / 200000000) (Real.log (13557 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (94370639 / 250000000) ≤ -Real.log (62500 / 91163) ∧
    -Real.log (62500 / 91163) ≤ (377482557 / 1000000000) := by
  have h := checkLog_sound (w := (28663 / 153663)) (n := 12)
    (lo := (94370639 / 250000000)) (hi := (377482557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91163 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91163 / 62500) = 1/(62500 / 91163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (94370639 / 250000000) (377482557 / 1000000000) (Real.log (91163 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (91163 / 62500) = -Real.log (62500 / 91163) := by
    rw [show ((91163 / 62500) : ℝ) = ((62500 / 91163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (306805839 / 500000000) ≤ -Real.log (33837 / 62500) ∧
    -Real.log (33837 / 62500) ≤ (613611679 / 1000000000) := by
  have h := checkLog_sound (w := (28663 / 96337)) (n := 12)
    (lo := (306805839 / 500000000)) (hi := (613611679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 33837) = 1/(33837 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-613611679 / 1000000000) (-306805839 / 500000000) (Real.log (33837 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (147649867 / 500000000) ≤ -Real.log (1000000 / 1343529) ∧
    -Real.log (1000000 / 1343529) ≤ (59059947 / 200000000) := by
  have h := checkLog_sound (w := (343529 / 2343529)) (n := 12)
    (lo := (147649867 / 500000000)) (hi := (59059947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1343529 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1343529 / 1000000) = 1/(1000000 / 1343529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (147649867 / 500000000) (59059947 / 200000000) (Real.log (1343529 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1343529 / 1000000) = -Real.log (1000000 / 1343529) := by
    rw [show ((1343529 / 1000000) : ℝ) = ((1000000 / 1343529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (420876759 / 1000000000) ≤ -Real.log (656471 / 1000000) ∧
    -Real.log (656471 / 1000000) ≤ (10521919 / 25000000) := by
  have h := checkLog_sound (w := (343529 / 1656471)) (n := 12)
    (lo := (420876759 / 1000000000)) (hi := (10521919 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 656471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 656471) = 1/(656471 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10521919 / 25000000) (-420876759 / 1000000000) (Real.log (656471 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (59171413 / 200000000) ≤ -Real.log (500000 / 672139) ∧
    -Real.log (500000 / 672139) ≤ (147928533 / 500000000) := by
  have h := checkLog_sound (w := (172139 / 1172139)) (n := 12)
    (lo := (59171413 / 200000000)) (hi := (147928533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((672139 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(672139 / 500000) = 1/(500000 / 672139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (59171413 / 200000000) (147928533 / 500000000) (Real.log (672139 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (672139 / 500000) = -Real.log (500000 / 672139) := by
    rw [show ((672139 / 500000) : ℝ) = ((500000 / 672139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (10550459 / 25000000) ≤ -Real.log (327861 / 500000) ∧
    -Real.log (327861 / 500000) ≤ (422018361 / 1000000000) := by
  have h := checkLog_sound (w := (172139 / 827861)) (n := 12)
    (lo := (10550459 / 25000000)) (hi := (422018361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 327861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 327861) = 1/(327861 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-422018361 / 1000000000) (-10550459 / 25000000) (Real.log (327861 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (123605797 / 125000000) ≤ -Real.log (500000000000 / 1344065796267) ∧
    -Real.log (500000000000 / 1344065796267) ≤ (494423189 / 500000000) := by
  have h := checkLog_sound (w := (344065796267 / 2344065796267)) (n := 12)
    (lo := (73924799 / 250000000)) (hi := (295699197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1344065796267 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1344065796267 / 1000000000000) = 1/(500000000000 / 1344065796267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (123605797 / 125000000) (494423189 / 500000000) (Real.log (1344065796267 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1344065796267 / 500000000000) = -Real.log (500000000000 / 1344065796267) := by
    rw [show ((1344065796267 / 500000000000) : ℝ) = ((500000000000 / 1344065796267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (495547117 / 500000000) ≤ -Real.log (500000000000 / 1347090463103) ∧
    -Real.log (500000000000 / 1347090463103) ≤ (247773559 / 250000000) := by
  have h := checkLog_sound (w := (347090463103 / 2347090463103)) (n := 12)
    (lo := (148973527 / 500000000)) (hi := (59589411 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347090463103 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1347090463103 / 1000000000000) = 1/(500000000000 / 1347090463103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (495547117 / 500000000) (247773559 / 250000000) (Real.log (1347090463103 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1347090463103 / 500000000000) = -Real.log (500000000000 / 1347090463103) := by
    rw [show ((1347090463103 / 500000000000) : ℝ) = ((500000000000 / 1347090463103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (716176493 / 1000000000) ≤ -Real.log (250000000000 / 511648267783) ∧
    -Real.log (250000000000 / 511648267783) ≤ (143235299 / 200000000) := by
  have h := checkLog_sound (w := (11648267783 / 1011648267783)) (n := 12)
    (lo := (23029313 / 1000000000)) (hi := (11514657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((511648267783 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(511648267783 / 500000000000) = 1/(250000000000 / 511648267783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (716176493 / 1000000000) (143235299 / 200000000) (Real.log (511648267783 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (511648267783 / 250000000000) = -Real.log (250000000000 / 511648267783) := by
    rw [show ((511648267783 / 250000000000) : ℝ) = ((250000000000 / 511648267783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (28715017 / 40000000) ≤ -Real.log (4000000000 / 8200292197) ∧
    -Real.log (4000000000 / 8200292197) ≤ (717875427 / 1000000000) := by
  have h := checkLog_sound (w := (200292197 / 16200292197)) (n := 12)
    (lo := (4945649 / 200000000)) (hi := (12364123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8200292197 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8200292197 / 8000000000) = 1/(4000000000 / 8200292197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (28715017 / 40000000) (717875427 / 1000000000) (Real.log (8200292197 / 4000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8200292197 / 4000000000) = -Real.log (4000000000 / 8200292197) := by
    rw [show ((8200292197 / 4000000000) : ℝ) = ((4000000000 / 8200292197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0177

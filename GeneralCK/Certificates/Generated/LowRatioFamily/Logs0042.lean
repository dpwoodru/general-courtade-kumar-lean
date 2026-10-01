import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2688_neg : (185727349 / 1000000000) ≤ -Real.log (1661 / 2000) ∧
    -Real.log (1661 / 2000) ≤ (3714547 / 20000000) := by
  have h := checkLog_sound (w := (339 / 3661)) (n := 12)
    (lo := (185727349 / 1000000000)) (hi := (3714547 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1661) = 1/(1661 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2688 : Bounds (-3714547 / 20000000) (-185727349 / 1000000000) (Real.log (1661 / 2000)) := by
  have h := reflection_log_2688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2689_neg : (33897 / 200000000) ≤ -Real.log (2000000 / 2000339) ∧
    -Real.log (2000000 / 2000339) ≤ (84743 / 500000000) := by
  have h := checkLog_sound (w := (339 / 4000339)) (n := 12)
    (lo := (33897 / 200000000)) (hi := (84743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000339 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000339 / 2000000) = 1/(2000000 / 2000339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2689 : Bounds (33897 / 200000000) (84743 / 500000000) (Real.log (2000339 / 2000000)) := by
  have h := reflection_log_2689_neg
  have he : Real.log (2000339 / 2000000) = -Real.log (2000000 / 2000339) := by
    rw [show ((2000339 / 2000000) : ℝ) = ((2000000 / 2000339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2690_neg : (84757 / 500000000) ≤ -Real.log (1999661 / 2000000) ∧
    -Real.log (1999661 / 2000000) ≤ (33903 / 200000000) := by
  have h := checkLog_sound (w := (339 / 3999661)) (n := 12)
    (lo := (84757 / 500000000)) (hi := (33903 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999661) = 1/(1999661 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2690 : Bounds (-33903 / 200000000) (-84757 / 500000000) (Real.log (1999661 / 2000000)) := by
  have h := reflection_log_2690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2691_neg : (2040813 / 25000000) ≤ -Real.log (1000000 / 1085057) ∧
    -Real.log (1000000 / 1085057) ≤ (81632521 / 1000000000) := by
  have h := checkLog_sound (w := (85057 / 2085057)) (n := 12)
    (lo := (2040813 / 25000000)) (hi := (81632521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085057 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085057 / 1000000) = 1/(1000000 / 1085057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2691 : Bounds (2040813 / 25000000) (81632521 / 1000000000) (Real.log (1085057 / 1000000)) := by
  have h := reflection_log_2691_neg
  have he : Real.log (1085057 / 1000000) = -Real.log (1000000 / 1085057) := by
    rw [show ((1085057 / 1000000) : ℝ) = ((1000000 / 1085057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2692_neg : (8889351 / 100000000) ≤ -Real.log (914943 / 1000000) ∧
    -Real.log (914943 / 1000000) ≤ (88893511 / 1000000000) := by
  have h := checkLog_sound (w := (85057 / 1914943)) (n := 12)
    (lo := (8889351 / 100000000)) (hi := (88893511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914943) = 1/(914943 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2692 : Bounds (-88893511 / 1000000000) (-8889351 / 100000000) (Real.log (914943 / 1000000)) := by
  have h := reflection_log_2692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2693_neg : (3273447 / 40000000) ≤ -Real.log (500000 / 542639) ∧
    -Real.log (500000 / 542639) ≤ (5114761 / 62500000) := by
  have h := checkLog_sound (w := (42639 / 1042639)) (n := 12)
    (lo := (3273447 / 40000000)) (hi := (5114761 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542639 / 500000) = 1/(500000 / 542639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2693 : Bounds (3273447 / 40000000) (5114761 / 62500000) (Real.log (542639 / 500000)) := by
  have h := reflection_log_2693_neg
  have he : Real.log (542639 / 500000) = -Real.log (500000 / 542639) := by
    rw [show ((542639 / 500000) : ℝ) = ((500000 / 542639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2694_neg : (17827017 / 200000000) ≤ -Real.log (457361 / 500000) ∧
    -Real.log (457361 / 500000) ≤ (44567543 / 500000000) := by
  have h := checkLog_sound (w := (42639 / 957361)) (n := 12)
    (lo := (17827017 / 200000000)) (hi := (44567543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457361) = 1/(457361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2694 : Bounds (-44567543 / 500000000) (-17827017 / 200000000) (Real.log (457361 / 500000)) := by
  have h := reflection_log_2694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2695_neg : (7298909 / 1000000000) ≤ -Real.log (248181915679 / 250000000000) ∧
    -Real.log (248181915679 / 250000000000) ≤ (729891 / 100000000) := by
  have h := checkLog_sound (w := (1818084321 / 498181915679)) (n := 12)
    (lo := (7298909 / 1000000000)) (hi := (729891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248181915679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248181915679) = 1/(248181915679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2695 : Bounds (-729891 / 100000000) (-7298909 / 1000000000) (Real.log (248181915679 / 250000000000)) := by
  have h := reflection_log_2695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2696_neg : (726099 / 100000000) ≤ -Real.log (992765306751 / 1000000000000) ∧
    -Real.log (992765306751 / 1000000000000) ≤ (7260991 / 1000000000) := by
  have h := checkLog_sound (w := (7234693249 / 1992765306751)) (n := 12)
    (lo := (726099 / 100000000)) (hi := (7260991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992765306751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992765306751) = 1/(992765306751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2696 : Bounds (-7260991 / 1000000000) (-726099 / 100000000) (Real.log (992765306751 / 1000000000000)) := by
  have h := reflection_log_2696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2697_neg : (17052603 / 100000000) ≤ -Real.log (500000000000 / 592964261161) ∧
    -Real.log (500000000000 / 592964261161) ≤ (170526031 / 1000000000) := by
  have h := checkLog_sound (w := (92964261161 / 1092964261161)) (n := 12)
    (lo := (17052603 / 100000000)) (hi := (170526031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592964261161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592964261161 / 500000000000) = 1/(500000000000 / 592964261161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2697 : Bounds (17052603 / 100000000) (170526031 / 1000000000) (Real.log (592964261161 / 500000000000)) := by
  have h := reflection_log_2697_neg
  have he : Real.log (592964261161 / 500000000000) = -Real.log (500000000000 / 592964261161) := by
    rw [show ((592964261161 / 500000000000) : ℝ) = ((500000000000 / 592964261161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2698_neg : (8548563 / 50000000) ≤ -Real.log (500000000000 / 593228325109) ∧
    -Real.log (500000000000 / 593228325109) ≤ (170971261 / 1000000000) := by
  have h := checkLog_sound (w := (93228325109 / 1093228325109)) (n := 12)
    (lo := (8548563 / 50000000)) (hi := (170971261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593228325109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593228325109 / 500000000000) = 1/(500000000000 / 593228325109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2698 : Bounds (8548563 / 50000000) (170971261 / 1000000000) (Real.log (593228325109 / 500000000000)) := by
  have h := reflection_log_2698_neg
  have he : Real.log (593228325109 / 500000000000) = -Real.log (500000000000 / 593228325109) := by
    rw [show ((593228325109 / 500000000000) : ℝ) = ((500000000000 / 593228325109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2699_neg : (21381109 / 62500000) ≤ -Real.log (125000000000 / 175987238141) ∧
    -Real.log (125000000000 / 175987238141) ≤ (68419549 / 200000000) := by
  have h := checkLog_sound (w := (50987238141 / 300987238141)) (n := 12)
    (lo := (21381109 / 62500000)) (hi := (68419549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175987238141 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175987238141 / 125000000000) = 1/(125000000000 / 175987238141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2699 : Bounds (21381109 / 62500000) (68419549 / 200000000) (Real.log (175987238141 / 125000000000)) := by
  have h := reflection_log_2699_neg
  have he : Real.log (175987238141 / 125000000000) = -Real.log (125000000000 / 175987238141) := by
    rw [show ((175987238141 / 125000000000) : ℝ) = ((125000000000 / 175987238141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2700_neg : (42787957 / 125000000) ≤ -Real.log (250000000000 / 352046959663) ∧
    -Real.log (250000000000 / 352046959663) ≤ (342303657 / 1000000000) := by
  have h := checkLog_sound (w := (102046959663 / 602046959663)) (n := 12)
    (lo := (42787957 / 125000000)) (hi := (342303657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352046959663 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352046959663 / 250000000000) = 1/(250000000000 / 352046959663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2700 : Bounds (42787957 / 125000000) (342303657 / 1000000000) (Real.log (352046959663 / 250000000000)) := by
  have h := reflection_log_2700_neg
  have he : Real.log (352046959663 / 250000000000) = -Real.log (250000000000 / 352046959663) := by
    rw [show ((352046959663 / 250000000000) : ℝ) = ((250000000000 / 352046959663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2701_neg : (15666181 / 100000000) ≤ -Real.log (625 / 731) ∧
    -Real.log (625 / 731) ≤ (156661811 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 678)) (n := 12)
    (lo := (15666181 / 100000000)) (hi := (156661811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731 / 625) = 1/(625 / 731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2701 : Bounds (15666181 / 100000000) (156661811 / 1000000000) (Real.log (731 / 625)) := by
  have h := reflection_log_2701_neg
  have he : Real.log (731 / 625) = -Real.log (625 / 731) := by
    rw [show ((731 / 625) : ℝ) = ((625 / 731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2702_neg : (92923883 / 500000000) ≤ -Real.log (519 / 625) ∧
    -Real.log (519 / 625) ≤ (185847767 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 572)) (n := 12)
    (lo := (92923883 / 500000000)) (hi := (185847767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 519) = 1/(519 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2702 : Bounds (-185847767 / 1000000000) (-92923883 / 500000000) (Real.log (519 / 625)) := by
  have h := reflection_log_2702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2703_neg : (33917 / 200000000) ≤ -Real.log (312500 / 312553) ∧
    -Real.log (312500 / 312553) ≤ (84793 / 500000000) := by
  have h := checkLog_sound (w := (53 / 625053)) (n := 12)
    (lo := (33917 / 200000000)) (hi := (84793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312553 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312553 / 312500) = 1/(312500 / 312553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2703 : Bounds (33917 / 200000000) (84793 / 500000000) (Real.log (312553 / 312500)) := by
  have h := reflection_log_2703_neg
  have he : Real.log (312553 / 312500) = -Real.log (312500 / 312553) := by
    rw [show ((312553 / 312500) : ℝ) = ((312500 / 312553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2704_neg : (84807 / 500000000) ≤ -Real.log (312447 / 312500) ∧
    -Real.log (312447 / 312500) ≤ (33923 / 200000000) := by
  have h := checkLog_sound (w := (53 / 624947)) (n := 12)
    (lo := (84807 / 500000000)) (hi := (33923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312447) = 1/(312447 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2704 : Bounds (-33923 / 200000000) (-84807 / 500000000) (Real.log (312447 / 312500)) := by
  have h := reflection_log_2704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2705_neg : (81679521 / 1000000000) ≤ -Real.log (250000 / 271277) ∧
    -Real.log (250000 / 271277) ≤ (40839761 / 500000000) := by
  have h := checkLog_sound (w := (21277 / 521277)) (n := 12)
    (lo := (81679521 / 1000000000)) (hi := (40839761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271277 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271277 / 250000) = 1/(250000 / 271277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2705 : Bounds (81679521 / 1000000000) (40839761 / 500000000) (Real.log (271277 / 250000)) := by
  have h := reflection_log_2705_neg
  have he : Real.log (271277 / 250000) = -Real.log (250000 / 271277) := by
    rw [show ((271277 / 250000) : ℝ) = ((250000 / 271277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2706_neg : (88949253 / 1000000000) ≤ -Real.log (228723 / 250000) ∧
    -Real.log (228723 / 250000) ≤ (44474627 / 500000000) := by
  have h := checkLog_sound (w := (21277 / 478723)) (n := 12)
    (lo := (88949253 / 1000000000)) (hi := (44474627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228723) = 1/(228723 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2706 : Bounds (-44474627 / 500000000) (-88949253 / 1000000000) (Real.log (228723 / 250000)) := by
  have h := reflection_log_2706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2707_neg : (16376449 / 200000000) ≤ -Real.log (62500 / 67833) ∧
    -Real.log (62500 / 67833) ≤ (40941123 / 500000000) := by
  have h := checkLog_sound (w := (5333 / 130333)) (n := 12)
    (lo := (16376449 / 200000000)) (hi := (40941123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67833 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67833 / 62500) = 1/(62500 / 67833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2707 : Bounds (16376449 / 200000000) (40941123 / 500000000) (Real.log (67833 / 62500)) := by
  have h := reflection_log_2707_neg
  have he : Real.log (67833 / 62500) = -Real.log (62500 / 67833) := by
    rw [show ((67833 / 62500) : ℝ) = ((62500 / 67833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2708_neg : (89189747 / 1000000000) ≤ -Real.log (57167 / 62500) ∧
    -Real.log (57167 / 62500) ≤ (22297437 / 250000000) := by
  have h := checkLog_sound (w := (5333 / 119667)) (n := 12)
    (lo := (89189747 / 1000000000)) (hi := (22297437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57167) = 1/(57167 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2708 : Bounds (-22297437 / 250000000) (-89189747 / 1000000000) (Real.log (57167 / 62500)) := by
  have h := reflection_log_2708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2709_neg : (3653751 / 500000000) ≤ -Real.log (3877809111 / 3906250000) ∧
    -Real.log (3877809111 / 3906250000) ≤ (7307503 / 1000000000) := by
  have h := checkLog_sound (w := (28440889 / 7784059111)) (n := 12)
    (lo := (3653751 / 500000000)) (hi := (7307503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3877809111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3877809111) = 1/(3877809111 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2709 : Bounds (-7307503 / 1000000000) (-3653751 / 500000000) (Real.log (3877809111 / 3906250000)) := by
  have h := reflection_log_2709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2710_neg : (1817433 / 250000000) ≤ -Real.log (62047289271 / 62500000000) ∧
    -Real.log (62047289271 / 62500000000) ≤ (7269733 / 1000000000) := by
  have h := checkLog_sound (w := (452710729 / 124547289271)) (n := 12)
    (lo := (1817433 / 250000000)) (hi := (7269733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62047289271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62047289271) = 1/(62047289271 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2710 : Bounds (-7269733 / 1000000000) (-1817433 / 250000000) (Real.log (62047289271 / 62500000000)) := by
  have h := reflection_log_2710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2711_neg : (85314387 / 500000000) ≤ -Real.log (62500000000 / 74128148459) ∧
    -Real.log (62500000000 / 74128148459) ≤ (6825151 / 40000000) := by
  have h := checkLog_sound (w := (11628148459 / 136628148459)) (n := 12)
    (lo := (85314387 / 500000000)) (hi := (6825151 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74128148459 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74128148459 / 62500000000) = 1/(62500000000 / 74128148459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2711 : Bounds (85314387 / 500000000) (6825151 / 40000000) (Real.log (74128148459 / 62500000000)) := by
  have h := reflection_log_2711_neg
  have he : Real.log (74128148459 / 62500000000) = -Real.log (62500000000 / 74128148459) := by
    rw [show ((74128148459 / 62500000000) : ℝ) = ((62500000000 / 74128148459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2712_neg : (171071993 / 1000000000) ≤ -Real.log (62500000000 / 74161010723) ∧
    -Real.log (62500000000 / 74161010723) ≤ (85535997 / 500000000) := by
  have h := checkLog_sound (w := (11661010723 / 136661010723)) (n := 12)
    (lo := (171071993 / 1000000000)) (hi := (85535997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74161010723 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74161010723 / 62500000000) = 1/(62500000000 / 74161010723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2712 : Bounds (171071993 / 1000000000) (85535997 / 500000000) (Real.log (74161010723 / 62500000000)) := by
  have h := reflection_log_2712_neg
  have he : Real.log (74161010723 / 62500000000) = -Real.log (62500000000 / 74161010723) := by
    rw [show ((74161010723 / 62500000000) : ℝ) = ((62500000000 / 74161010723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2713_neg : (42787957 / 125000000) ≤ -Real.log (20000000000 / 28163756773) ∧
    -Real.log (20000000000 / 28163756773) ≤ (342303657 / 1000000000) := by
  have h := checkLog_sound (w := (8163756773 / 48163756773)) (n := 12)
    (lo := (42787957 / 125000000)) (hi := (342303657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28163756773 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28163756773 / 20000000000) = 1/(20000000000 / 28163756773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2713 : Bounds (42787957 / 125000000) (342303657 / 1000000000) (Real.log (28163756773 / 20000000000)) := by
  have h := reflection_log_2713_neg
  have he : Real.log (28163756773 / 20000000000) = -Real.log (20000000000 / 28163756773) := by
    rw [show ((28163756773 / 20000000000) : ℝ) = ((20000000000 / 28163756773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2714_neg : (42813697 / 125000000) ≤ -Real.log (250000000000 / 352119460501) ∧
    -Real.log (250000000000 / 352119460501) ≤ (342509577 / 1000000000) := by
  have h := checkLog_sound (w := (102119460501 / 602119460501)) (n := 12)
    (lo := (42813697 / 125000000)) (hi := (342509577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352119460501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352119460501 / 250000000000) = 1/(250000000000 / 352119460501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2714 : Bounds (42813697 / 125000000) (342509577 / 1000000000) (Real.log (352119460501 / 250000000000)) := by
  have h := reflection_log_2714_neg
  have he : Real.log (352119460501 / 250000000000) = -Real.log (250000000000 / 352119460501) := by
    rw [show ((352119460501 / 250000000000) : ℝ) = ((250000000000 / 352119460501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2715_neg : (31349461 / 200000000) ≤ -Real.log (10000 / 11697) ∧
    -Real.log (10000 / 11697) ≤ (78373653 / 500000000) := by
  have h := checkLog_sound (w := (1697 / 21697)) (n := 12)
    (lo := (31349461 / 200000000)) (hi := (78373653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11697 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11697 / 10000) = 1/(10000 / 11697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2715 : Bounds (31349461 / 200000000) (78373653 / 500000000) (Real.log (11697 / 10000)) := by
  have h := reflection_log_2715_neg
  have he : Real.log (11697 / 10000) = -Real.log (10000 / 11697) := by
    rw [show ((11697 / 10000) : ℝ) = ((10000 / 11697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2716_neg : (185968197 / 1000000000) ≤ -Real.log (8303 / 10000) ∧
    -Real.log (8303 / 10000) ≤ (92984099 / 500000000) := by
  have h := checkLog_sound (w := (1697 / 18303)) (n := 12)
    (lo := (185968197 / 1000000000)) (hi := (92984099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8303) = 1/(8303 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2716 : Bounds (-92984099 / 500000000) (-185968197 / 1000000000) (Real.log (8303 / 10000)) := by
  have h := reflection_log_2716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2717_neg : (33937 / 200000000) ≤ -Real.log (10000000 / 10001697) ∧
    -Real.log (10000000 / 10001697) ≤ (84843 / 500000000) := by
  have h := checkLog_sound (w := (1697 / 20001697)) (n := 12)
    (lo := (33937 / 200000000)) (hi := (84843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001697 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001697 / 10000000) = 1/(10000000 / 10001697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2717 : Bounds (33937 / 200000000) (84843 / 500000000) (Real.log (10001697 / 10000000)) := by
  have h := reflection_log_2717_neg
  have he : Real.log (10001697 / 10000000) = -Real.log (10000000 / 10001697) := by
    rw [show ((10001697 / 10000000) : ℝ) = ((10000000 / 10001697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2718_neg : (84857 / 500000000) ≤ -Real.log (9998303 / 10000000) ∧
    -Real.log (9998303 / 10000000) ≤ (33943 / 200000000) := by
  have h := checkLog_sound (w := (1697 / 19998303)) (n := 12)
    (lo := (84857 / 500000000)) (hi := (33943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998303) = 1/(9998303 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2718 : Bounds (-33943 / 200000000) (-84857 / 500000000) (Real.log (9998303 / 10000000)) := by
  have h := reflection_log_2718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2719_neg : (2043163 / 25000000) ≤ -Real.log (1000000 / 1085159) ∧
    -Real.log (1000000 / 1085159) ≤ (81726521 / 1000000000) := by
  have h := checkLog_sound (w := (85159 / 2085159)) (n := 12)
    (lo := (2043163 / 25000000)) (hi := (81726521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085159 / 1000000) = 1/(1000000 / 1085159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2719 : Bounds (2043163 / 25000000) (81726521 / 1000000000) (Real.log (1085159 / 1000000)) := by
  have h := reflection_log_2719_neg
  have he : Real.log (1085159 / 1000000) = -Real.log (1000000 / 1085159) := by
    rw [show ((1085159 / 1000000) : ℝ) = ((1000000 / 1085159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2720_neg : (89004999 / 1000000000) ≤ -Real.log (914841 / 1000000) ∧
    -Real.log (914841 / 1000000) ≤ (17801 / 200000) := by
  have h := checkLog_sound (w := (85159 / 1914841)) (n := 12)
    (lo := (89004999 / 1000000000)) (hi := (17801 / 200000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914841) = 1/(914841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2720 : Bounds (-17801 / 200000) (-89004999 / 1000000000) (Real.log (914841 / 1000000)) := by
  have h := reflection_log_2720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2721_neg : (40964617 / 500000000) ≤ -Real.log (1000000 / 1085379) ∧
    -Real.log (1000000 / 1085379) ≤ (16385847 / 200000000) := by
  have h := checkLog_sound (w := (85379 / 2085379)) (n := 12)
    (lo := (40964617 / 500000000)) (hi := (16385847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085379 / 1000000) = 1/(1000000 / 1085379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2721 : Bounds (40964617 / 500000000) (16385847 / 200000000) (Real.log (1085379 / 1000000)) := by
  have h := reflection_log_2721_neg
  have he : Real.log (1085379 / 1000000) = -Real.log (1000000 / 1085379) := by
    rw [show ((1085379 / 1000000) : ℝ) = ((1000000 / 1085379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2722_neg : (89245507 / 1000000000) ≤ -Real.log (914621 / 1000000) ∧
    -Real.log (914621 / 1000000) ≤ (22311377 / 250000000) := by
  have h := checkLog_sound (w := (85379 / 1914621)) (n := 12)
    (lo := (89245507 / 1000000000)) (hi := (22311377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914621) = 1/(914621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2722 : Bounds (-22311377 / 250000000) (-89245507 / 1000000000) (Real.log (914621 / 1000000)) := by
  have h := reflection_log_2722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2723_neg : (457267 / 62500000) ≤ -Real.log (992710426359 / 1000000000000) ∧
    -Real.log (992710426359 / 1000000000000) ≤ (7316273 / 1000000000) := by
  have h := checkLog_sound (w := (7289573641 / 1992710426359)) (n := 12)
    (lo := (457267 / 62500000)) (hi := (7316273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992710426359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992710426359) = 1/(992710426359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2723 : Bounds (-7316273 / 1000000000) (-457267 / 62500000) (Real.log (992710426359 / 1000000000000)) := by
  have h := reflection_log_2723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2724_neg : (7278479 / 1000000000) ≤ -Real.log (992747944719 / 1000000000000) ∧
    -Real.log (992747944719 / 1000000000000) ≤ (90981 / 12500000) := by
  have h := checkLog_sound (w := (7252055281 / 1992747944719)) (n := 12)
    (lo := (7278479 / 1000000000)) (hi := (90981 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992747944719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992747944719) = 1/(992747944719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2724 : Bounds (-90981 / 12500000) (-7278479 / 1000000000) (Real.log (992747944719 / 1000000000000)) := by
  have h := reflection_log_2724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2725_neg : (170731519 / 1000000000) ≤ -Real.log (31250000000 / 37067882561) ∧
    -Real.log (31250000000 / 37067882561) ≤ (66692 / 390625) := by
  have h := checkLog_sound (w := (5817882561 / 68317882561)) (n := 12)
    (lo := (170731519 / 1000000000)) (hi := (66692 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37067882561 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37067882561 / 31250000000) = 1/(31250000000 / 37067882561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2725 : Bounds (170731519 / 1000000000) (66692 / 390625) (Real.log (37067882561 / 31250000000)) := by
  have h := reflection_log_2725_neg
  have he : Real.log (37067882561 / 31250000000) = -Real.log (31250000000 / 37067882561) := by
    rw [show ((37067882561 / 31250000000) : ℝ) = ((31250000000 / 37067882561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2726_neg : (171174741 / 1000000000) ≤ -Real.log (125000000000 / 148337262101) ∧
    -Real.log (125000000000 / 148337262101) ≤ (85587371 / 500000000) := by
  have h := checkLog_sound (w := (23337262101 / 273337262101)) (n := 12)
    (lo := (171174741 / 1000000000)) (hi := (85587371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148337262101 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148337262101 / 125000000000) = 1/(125000000000 / 148337262101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2726 : Bounds (171174741 / 1000000000) (85587371 / 500000000) (Real.log (148337262101 / 125000000000)) := by
  have h := reflection_log_2726_neg
  have he : Real.log (148337262101 / 125000000000) = -Real.log (125000000000 / 148337262101) := by
    rw [show ((148337262101 / 125000000000) : ℝ) = ((125000000000 / 148337262101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2727_neg : (42813697 / 125000000) ≤ -Real.log (500000000000 / 704238921001) ∧
    -Real.log (500000000000 / 704238921001) ≤ (342509577 / 1000000000) := by
  have h := checkLog_sound (w := (204238921001 / 1204238921001)) (n := 12)
    (lo := (42813697 / 125000000)) (hi := (342509577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704238921001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704238921001 / 500000000000) = 1/(500000000000 / 704238921001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2727 : Bounds (42813697 / 125000000) (342509577 / 1000000000) (Real.log (704238921001 / 500000000000)) := by
  have h := reflection_log_2727_neg
  have he : Real.log (704238921001 / 500000000000) = -Real.log (500000000000 / 704238921001) := by
    rw [show ((704238921001 / 500000000000) : ℝ) = ((500000000000 / 704238921001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2728_neg : (342715503 / 1000000000) ≤ -Real.log (250000000000 / 352191978803) ∧
    -Real.log (250000000000 / 352191978803) ≤ (21419719 / 62500000) := by
  have h := checkLog_sound (w := (102191978803 / 602191978803)) (n := 12)
    (lo := (342715503 / 1000000000)) (hi := (21419719 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352191978803 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352191978803 / 250000000000) = 1/(250000000000 / 352191978803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2728 : Bounds (342715503 / 1000000000) (21419719 / 62500000) (Real.log (352191978803 / 250000000000)) := by
  have h := reflection_log_2728_neg
  have he : Real.log (352191978803 / 250000000000) = -Real.log (250000000000 / 352191978803) := by
    rw [show ((352191978803 / 250000000000) : ℝ) = ((250000000000 / 352191978803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2729_neg : (78416397 / 500000000) ≤ -Real.log (5000 / 5849) ∧
    -Real.log (5000 / 5849) ≤ (31366559 / 200000000) := by
  have h := checkLog_sound (w := (849 / 10849)) (n := 12)
    (lo := (78416397 / 500000000)) (hi := (31366559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5849 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5849 / 5000) = 1/(5000 / 5849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2729 : Bounds (78416397 / 500000000) (31366559 / 200000000) (Real.log (5849 / 5000)) := by
  have h := reflection_log_2729_neg
  have he : Real.log (5849 / 5000) = -Real.log (5000 / 5849) := by
    rw [show ((5849 / 5000) : ℝ) = ((5000 / 5849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2730_neg : (186088643 / 1000000000) ≤ -Real.log (4151 / 5000) ∧
    -Real.log (4151 / 5000) ≤ (46522161 / 250000000) := by
  have h := checkLog_sound (w := (849 / 9151)) (n := 12)
    (lo := (186088643 / 1000000000)) (hi := (46522161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4151) = 1/(4151 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2730 : Bounds (-46522161 / 250000000) (-186088643 / 1000000000) (Real.log (4151 / 5000)) := by
  have h := reflection_log_2730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2731_neg : (33957 / 200000000) ≤ -Real.log (5000000 / 5000849) ∧
    -Real.log (5000000 / 5000849) ≤ (84893 / 500000000) := by
  have h := checkLog_sound (w := (849 / 10000849)) (n := 12)
    (lo := (33957 / 200000000)) (hi := (84893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000849 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000849 / 5000000) = 1/(5000000 / 5000849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2731 : Bounds (33957 / 200000000) (84893 / 500000000) (Real.log (5000849 / 5000000)) := by
  have h := reflection_log_2731_neg
  have he : Real.log (5000849 / 5000000) = -Real.log (5000000 / 5000849) := by
    rw [show ((5000849 / 5000000) : ℝ) = ((5000000 / 5000849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2732_neg : (84907 / 500000000) ≤ -Real.log (4999151 / 5000000) ∧
    -Real.log (4999151 / 5000000) ≤ (33963 / 200000000) := by
  have h := checkLog_sound (w := (849 / 9999151)) (n := 12)
    (lo := (84907 / 500000000)) (hi := (33963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999151) = 1/(4999151 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2732 : Bounds (-33963 / 200000000) (-84907 / 500000000) (Real.log (4999151 / 5000000)) := by
  have h := reflection_log_2732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2733_neg : (20443379 / 250000000) ≤ -Real.log (100000 / 108521) ∧
    -Real.log (100000 / 108521) ≤ (81773517 / 1000000000) := by
  have h := checkLog_sound (w := (8521 / 208521)) (n := 12)
    (lo := (20443379 / 250000000)) (hi := (81773517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108521 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108521 / 100000) = 1/(100000 / 108521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2733 : Bounds (20443379 / 250000000) (81773517 / 1000000000) (Real.log (108521 / 100000)) := by
  have h := reflection_log_2733_neg
  have he : Real.log (108521 / 100000) = -Real.log (100000 / 108521) := by
    rw [show ((108521 / 100000) : ℝ) = ((100000 / 108521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2734_neg : (22265187 / 250000000) ≤ -Real.log (91479 / 100000) ∧
    -Real.log (91479 / 100000) ≤ (89060749 / 1000000000) := by
  have h := checkLog_sound (w := (8521 / 191479)) (n := 12)
    (lo := (22265187 / 250000000)) (hi := (89060749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91479) = 1/(91479 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2734 : Bounds (-89060749 / 1000000000) (-22265187 / 250000000) (Real.log (91479 / 100000)) := by
  have h := reflection_log_2734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2735_neg : (81976221 / 1000000000) ≤ -Real.log (100000 / 108543) ∧
    -Real.log (100000 / 108543) ≤ (40988111 / 500000000) := by
  have h := checkLog_sound (w := (8543 / 208543)) (n := 12)
    (lo := (81976221 / 1000000000)) (hi := (40988111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108543 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108543 / 100000) = 1/(100000 / 108543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2735 : Bounds (81976221 / 1000000000) (40988111 / 500000000) (Real.log (108543 / 100000)) := by
  have h := reflection_log_2735_neg
  have he : Real.log (108543 / 100000) = -Real.log (100000 / 108543) := by
    rw [show ((108543 / 100000) : ℝ) = ((100000 / 108543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2736_neg : (89301269 / 1000000000) ≤ -Real.log (91457 / 100000) ∧
    -Real.log (91457 / 100000) ≤ (8930127 / 100000000) := by
  have h := checkLog_sound (w := (8543 / 191457)) (n := 12)
    (lo := (89301269 / 1000000000)) (hi := (8930127 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91457) = 1/(91457 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2736 : Bounds (-8930127 / 100000000) (-89301269 / 1000000000) (Real.log (91457 / 100000)) := by
  have h := reflection_log_2736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2737_neg : (7325047 / 1000000000) ≤ -Real.log (9927017151 / 10000000000) ∧
    -Real.log (9927017151 / 10000000000) ≤ (915631 / 125000000) := by
  have h := checkLog_sound (w := (72982849 / 19927017151)) (n := 12)
    (lo := (7325047 / 1000000000)) (hi := (915631 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9927017151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9927017151) = 1/(9927017151 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2737 : Bounds (-915631 / 125000000) (-7325047 / 1000000000) (Real.log (9927017151 / 10000000000)) := by
  have h := reflection_log_2737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2738_neg : (7287231 / 1000000000) ≤ -Real.log (9927392559 / 10000000000) ∧
    -Real.log (9927392559 / 10000000000) ≤ (113863 / 15625000) := by
  have h := checkLog_sound (w := (72607441 / 19927392559)) (n := 12)
    (lo := (7287231 / 1000000000)) (hi := (113863 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9927392559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9927392559) = 1/(9927392559 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2738 : Bounds (-113863 / 15625000) (-7287231 / 1000000000) (Real.log (9927392559 / 10000000000)) := by
  have h := reflection_log_2738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2739_neg : (21354283 / 125000000) ≤ -Real.log (250000000000 / 296573530537) ∧
    -Real.log (250000000000 / 296573530537) ≤ (34166853 / 200000000) := by
  have h := checkLog_sound (w := (46573530537 / 546573530537)) (n := 12)
    (lo := (21354283 / 125000000)) (hi := (34166853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296573530537 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296573530537 / 250000000000) = 1/(250000000000 / 296573530537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2739 : Bounds (21354283 / 125000000) (34166853 / 200000000) (Real.log (296573530537 / 250000000000)) := by
  have h := reflection_log_2739_neg
  have he : Real.log (296573530537 / 250000000000) = -Real.log (250000000000 / 296573530537) := by
    rw [show ((296573530537 / 250000000000) : ℝ) = ((250000000000 / 296573530537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2740_neg : (171277491 / 1000000000) ≤ -Real.log (500000000000 / 593410017823) ∧
    -Real.log (500000000000 / 593410017823) ≤ (42819373 / 250000000) := by
  have h := checkLog_sound (w := (93410017823 / 1093410017823)) (n := 12)
    (lo := (171277491 / 1000000000)) (hi := (42819373 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593410017823 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593410017823 / 500000000000) = 1/(500000000000 / 593410017823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2740 : Bounds (171277491 / 1000000000) (42819373 / 250000000) (Real.log (593410017823 / 500000000000)) := by
  have h := reflection_log_2740_neg
  have he : Real.log (593410017823 / 500000000000) = -Real.log (500000000000 / 593410017823) := by
    rw [show ((593410017823 / 500000000000) : ℝ) = ((500000000000 / 593410017823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2741_neg : (342715503 / 1000000000) ≤ -Real.log (100000000000 / 140876791521) ∧
    -Real.log (100000000000 / 140876791521) ≤ (21419719 / 62500000) := by
  have h := checkLog_sound (w := (40876791521 / 240876791521)) (n := 12)
    (lo := (342715503 / 1000000000)) (hi := (21419719 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140876791521 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140876791521 / 100000000000) = 1/(100000000000 / 140876791521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2741 : Bounds (342715503 / 1000000000) (21419719 / 62500000) (Real.log (140876791521 / 100000000000)) := by
  have h := reflection_log_2741_neg
  have he : Real.log (140876791521 / 100000000000) = -Real.log (100000000000 / 140876791521) := by
    rw [show ((140876791521 / 100000000000) : ℝ) = ((100000000000 / 140876791521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2742_neg : (342921437 / 1000000000) ≤ -Real.log (10000000000 / 14090580583) ∧
    -Real.log (10000000000 / 14090580583) ≤ (171460719 / 500000000) := by
  have h := checkLog_sound (w := (4090580583 / 24090580583)) (n := 12)
    (lo := (342921437 / 1000000000)) (hi := (171460719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14090580583 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14090580583 / 10000000000) = 1/(10000000000 / 14090580583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2742 : Bounds (342921437 / 1000000000) (171460719 / 500000000) (Real.log (14090580583 / 10000000000)) := by
  have h := reflection_log_2742_neg
  have he : Real.log (14090580583 / 10000000000) = -Real.log (10000000000 / 14090580583) := by
    rw [show ((14090580583 / 10000000000) : ℝ) = ((10000000000 / 14090580583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2743_neg : (6276731 / 40000000) ≤ -Real.log (10000 / 11699) ∧
    -Real.log (10000 / 11699) ≤ (39229569 / 250000000) := by
  have h := checkLog_sound (w := (1699 / 21699)) (n := 12)
    (lo := (6276731 / 40000000)) (hi := (39229569 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11699 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11699 / 10000) = 1/(10000 / 11699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2743 : Bounds (6276731 / 40000000) (39229569 / 250000000) (Real.log (11699 / 10000)) := by
  have h := reflection_log_2743_neg
  have he : Real.log (11699 / 10000) = -Real.log (10000 / 11699) := by
    rw [show ((11699 / 10000) : ℝ) = ((10000 / 11699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2744_neg : (186209103 / 1000000000) ≤ -Real.log (8301 / 10000) ∧
    -Real.log (8301 / 10000) ≤ (11638069 / 62500000) := by
  have h := checkLog_sound (w := (1699 / 18301)) (n := 12)
    (lo := (186209103 / 1000000000)) (hi := (11638069 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8301) = 1/(8301 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2744 : Bounds (-11638069 / 62500000) (-186209103 / 1000000000) (Real.log (8301 / 10000)) := by
  have h := reflection_log_2744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2745_neg : (33977 / 200000000) ≤ -Real.log (10000000 / 10001699) ∧
    -Real.log (10000000 / 10001699) ≤ (84943 / 500000000) := by
  have h := checkLog_sound (w := (1699 / 20001699)) (n := 12)
    (lo := (33977 / 200000000)) (hi := (84943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001699 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001699 / 10000000) = 1/(10000000 / 10001699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2745 : Bounds (33977 / 200000000) (84943 / 500000000) (Real.log (10001699 / 10000000)) := by
  have h := reflection_log_2745_neg
  have he : Real.log (10001699 / 10000000) = -Real.log (10000000 / 10001699) := by
    rw [show ((10001699 / 10000000) : ℝ) = ((10000000 / 10001699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2746_neg : (84957 / 500000000) ≤ -Real.log (9998301 / 10000000) ∧
    -Real.log (9998301 / 10000000) ≤ (33983 / 200000000) := by
  have h := checkLog_sound (w := (1699 / 19998301)) (n := 12)
    (lo := (84957 / 500000000)) (hi := (33983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998301) = 1/(9998301 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2746 : Bounds (-33983 / 200000000) (-84957 / 500000000) (Real.log (9998301 / 10000000)) := by
  have h := reflection_log_2746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2747_neg : (81819589 / 1000000000) ≤ -Real.log (50000 / 54263) ∧
    -Real.log (50000 / 54263) ≤ (8181959 / 100000000) := by
  have h := checkLog_sound (w := (4263 / 104263)) (n := 12)
    (lo := (81819589 / 1000000000)) (hi := (8181959 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54263 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54263 / 50000) = 1/(50000 / 54263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2747 : Bounds (81819589 / 1000000000) (8181959 / 100000000) (Real.log (54263 / 50000)) := by
  have h := reflection_log_2747_neg
  have he : Real.log (54263 / 50000) = -Real.log (50000 / 54263) := by
    rw [show ((54263 / 50000) : ℝ) = ((50000 / 54263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2748_neg : (89115407 / 1000000000) ≤ -Real.log (45737 / 50000) ∧
    -Real.log (45737 / 50000) ≤ (5569713 / 62500000) := by
  have h := checkLog_sound (w := (4263 / 95737)) (n := 12)
    (lo := (89115407 / 1000000000)) (hi := (5569713 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45737) = 1/(45737 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2748 : Bounds (-5569713 / 62500000) (-89115407 / 1000000000) (Real.log (45737 / 50000)) := by
  have h := reflection_log_2748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2749_neg : (41011603 / 500000000) ≤ -Real.log (1000000 / 1085481) ∧
    -Real.log (1000000 / 1085481) ≤ (82023207 / 1000000000) := by
  have h := checkLog_sound (w := (85481 / 2085481)) (n := 12)
    (lo := (41011603 / 500000000)) (hi := (82023207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085481 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085481 / 1000000) = 1/(1000000 / 1085481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2749 : Bounds (41011603 / 500000000) (82023207 / 1000000000) (Real.log (1085481 / 1000000)) := by
  have h := reflection_log_2749_neg
  have he : Real.log (1085481 / 1000000) = -Real.log (1000000 / 1085481) := by
    rw [show ((1085481 / 1000000) : ℝ) = ((1000000 / 1085481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2750_neg : (44678517 / 500000000) ≤ -Real.log (914519 / 1000000) ∧
    -Real.log (914519 / 1000000) ≤ (17871407 / 200000000) := by
  have h := checkLog_sound (w := (85481 / 1914519)) (n := 12)
    (lo := (44678517 / 500000000)) (hi := (17871407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914519) = 1/(914519 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2750 : Bounds (-17871407 / 200000000) (-44678517 / 500000000) (Real.log (914519 / 1000000)) := by
  have h := reflection_log_2750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2751_neg : (1833457 / 250000000) ≤ -Real.log (992692998639 / 1000000000000) ∧
    -Real.log (992692998639 / 1000000000000) ≤ (7333829 / 1000000000) := by
  have h := checkLog_sound (w := (7307001361 / 1992692998639)) (n := 12)
    (lo := (1833457 / 250000000)) (hi := (7333829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992692998639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992692998639) = 1/(992692998639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2751 : Bounds (-7333829 / 1000000000) (-1833457 / 250000000) (Real.log (992692998639 / 1000000000000)) := by
  have h := reflection_log_2751_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13824_neg : (2055478287 / 1000000000) ≤ -Real.log (500000000000 / 3905286343613) ∧
    -Real.log (500000000000 / 3905286343613) ≤ (205547829 / 100000000) := by
  have h := checkLog_sound (w := (1905286343613 / 5905286343613)) (n := 12)
    (lo := (669183927 / 1000000000)) (hi := (83647991 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3905286343613 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3905286343613 / 2000000000000) = 1/(500000000000 / 3905286343613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13824 : Bounds (2055478287 / 1000000000) (205547829 / 100000000) (Real.log (3905286343613 / 500000000000)) := by
  have h := reflection_log_13824_neg
  have he : Real.log (3905286343613 / 500000000000) = -Real.log (500000000000 / 3905286343613) := by
    rw [show ((3905286343613 / 500000000000) : ℝ) = ((500000000000 / 3905286343613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13825_neg : (143590911 / 250000000) ≤ -Real.log (125 / 222) ∧
    -Real.log (125 / 222) ≤ (114872729 / 200000000) := by
  have h := checkLog_sound (w := (97 / 347)) (n := 12)
    (lo := (143590911 / 250000000)) (hi := (114872729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222 / 125) = 1/(125 / 222) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13825 : Bounds (143590911 / 250000000) (114872729 / 200000000) (Real.log (222 / 125)) := by
  have h := reflection_log_13825_neg
  have he : Real.log (222 / 125) = -Real.log (125 / 222) := by
    rw [show ((222 / 125) : ℝ) = ((125 / 222) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13826_neg : (748054613 / 500000000) ≤ -Real.log (28 / 125) ∧
    -Real.log (28 / 125) ≤ (1496109229 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 237)) (n := 12)
    (lo := (54907433 / 500000000)) (hi := (109814867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 112) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 112) = 1/(28 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13826 : Bounds (-1496109229 / 1000000000) (-748054613 / 500000000) (Real.log (28 / 125)) := by
  have h := reflection_log_13826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13827_neg : (775699 / 1000000000) ≤ -Real.log (125000 / 125097) ∧
    -Real.log (125000 / 125097) ≤ (7757 / 10000000) := by
  have h := checkLog_sound (w := (97 / 250097)) (n := 12)
    (lo := (775699 / 1000000000)) (hi := (7757 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125097 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125097 / 125000) = 1/(125000 / 125097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13827 : Bounds (775699 / 1000000000) (7757 / 10000000) (Real.log (125097 / 125000)) := by
  have h := reflection_log_13827_neg
  have he : Real.log (125097 / 125000) = -Real.log (125000 / 125097) := by
    rw [show ((125097 / 125000) : ℝ) = ((125000 / 125097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13828_neg : (776301 / 1000000000) ≤ -Real.log (124903 / 125000) ∧
    -Real.log (124903 / 125000) ≤ (388151 / 500000000) := by
  have h := checkLog_sound (w := (97 / 249903)) (n := 12)
    (lo := (776301 / 1000000000)) (hi := (388151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124903) = 1/(124903 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13828 : Bounds (-388151 / 500000000) (-776301 / 1000000000) (Real.log (124903 / 125000)) := by
  have h := reflection_log_13828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13829_neg : (363288029 / 1000000000) ≤ -Real.log (20000 / 28761) ∧
    -Real.log (20000 / 28761) ≤ (36328803 / 100000000) := by
  have h := checkLog_sound (w := (8761 / 48761)) (n := 12)
    (lo := (363288029 / 1000000000)) (hi := (36328803 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28761 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28761 / 20000) = 1/(20000 / 28761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13829 : Bounds (363288029 / 1000000000) (36328803 / 100000000) (Real.log (28761 / 20000)) := by
  have h := reflection_log_13829_neg
  have he : Real.log (28761 / 20000) = -Real.log (20000 / 28761) := by
    rw [show ((28761 / 20000) : ℝ) = ((20000 / 28761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13830_neg : (576342401 / 1000000000) ≤ -Real.log (11239 / 20000) ∧
    -Real.log (11239 / 20000) ≤ (288171201 / 500000000) := by
  have h := checkLog_sound (w := (8761 / 31239)) (n := 12)
    (lo := (576342401 / 1000000000)) (hi := (288171201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 11239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 11239) = 1/(11239 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13830 : Bounds (-288171201 / 500000000) (-576342401 / 1000000000) (Real.log (11239 / 20000)) := by
  have h := reflection_log_13830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13831_neg : (91322011 / 250000000) ≤ -Real.log (1000000 / 1440929) ∧
    -Real.log (1000000 / 1440929) ≤ (73057609 / 200000000) := by
  have h := checkLog_sound (w := (440929 / 2440929)) (n := 12)
    (lo := (91322011 / 250000000)) (hi := (73057609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1440929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1440929 / 1000000) = 1/(1000000 / 1440929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13831 : Bounds (91322011 / 250000000) (73057609 / 200000000) (Real.log (1440929 / 1000000)) := by
  have h := reflection_log_13831_neg
  have he : Real.log (1440929 / 1000000) = -Real.log (1000000 / 1440929) := by
    rw [show ((1440929 / 1000000) : ℝ) = ((1000000 / 1440929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13832_neg : (581478801 / 1000000000) ≤ -Real.log (559071 / 1000000) ∧
    -Real.log (559071 / 1000000) ≤ (290739401 / 500000000) := by
  have h := checkLog_sound (w := (440929 / 1559071)) (n := 12)
    (lo := (581478801 / 1000000000)) (hi := (290739401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 559071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 559071) = 1/(559071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13832 : Bounds (-290739401 / 500000000) (-581478801 / 1000000000) (Real.log (559071 / 1000000)) := by
  have h := reflection_log_13832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13833_neg : (54047689 / 250000000) ≤ -Real.log (805581616959 / 1000000000000) ∧
    -Real.log (805581616959 / 1000000000000) ≤ (216190757 / 1000000000) := by
  have h := checkLog_sound (w := (194418383041 / 1805581616959)) (n := 12)
    (lo := (54047689 / 250000000)) (hi := (216190757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 805581616959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 805581616959) = 1/(805581616959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13833 : Bounds (-216190757 / 1000000000) (-54047689 / 250000000) (Real.log (805581616959 / 1000000000000)) := by
  have h := reflection_log_13833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13834_neg : (213054371 / 1000000000) ≤ -Real.log (323244879 / 400000000) ∧
    -Real.log (323244879 / 400000000) ≤ (53263593 / 250000000) := by
  have h := checkLog_sound (w := (76755121 / 723244879)) (n := 12)
    (lo := (213054371 / 1000000000)) (hi := (53263593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 323244879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 323244879) = 1/(323244879 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13834 : Bounds (-53263593 / 250000000) (-213054371 / 1000000000) (Real.log (323244879 / 400000000)) := by
  have h := reflection_log_13834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13835_neg : (939630429 / 1000000000) ≤ -Real.log (500000000000 / 1279517750689) ∧
    -Real.log (500000000000 / 1279517750689) ≤ (939630431 / 1000000000) := by
  have h := checkLog_sound (w := (279517750689 / 2279517750689)) (n := 12)
    (lo := (246483249 / 1000000000)) (hi := (985933 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1279517750689 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1279517750689 / 1000000000000) = 1/(500000000000 / 1279517750689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13835 : Bounds (939630429 / 1000000000) (939630431 / 1000000000) (Real.log (1279517750689 / 500000000000)) := by
  have h := reflection_log_13835_neg
  have he : Real.log (1279517750689 / 500000000000) = -Real.log (500000000000 / 1279517750689) := by
    rw [show ((1279517750689 / 500000000000) : ℝ) = ((500000000000 / 1279517750689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13836_neg : (189353369 / 200000000) ≤ -Real.log (250000000000 / 644340790347) ∧
    -Real.log (250000000000 / 644340790347) ≤ (946766847 / 1000000000) := by
  have h := checkLog_sound (w := (144340790347 / 1144340790347)) (n := 12)
    (lo := (50723933 / 200000000)) (hi := (126809833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644340790347 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(644340790347 / 500000000000) = 1/(250000000000 / 644340790347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13836 : Bounds (189353369 / 200000000) (946766847 / 1000000000) (Real.log (644340790347 / 250000000000)) := by
  have h := reflection_log_13836_neg
  have he : Real.log (644340790347 / 250000000000) = -Real.log (250000000000 / 644340790347) := by
    rw [show ((644340790347 / 250000000000) : ℝ) = ((250000000000 / 644340790347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13837_neg : (2055478287 / 1000000000) ≤ -Real.log (125000000000 / 976321585903) ∧
    -Real.log (125000000000 / 976321585903) ≤ (205547829 / 100000000) := by
  have h := checkLog_sound (w := (476321585903 / 1476321585903)) (n := 12)
    (lo := (669183927 / 1000000000)) (hi := (83647991 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976321585903 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(976321585903 / 500000000000) = 1/(125000000000 / 976321585903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13837 : Bounds (2055478287 / 1000000000) (205547829 / 100000000) (Real.log (976321585903 / 125000000000)) := by
  have h := reflection_log_13837_neg
  have he : Real.log (976321585903 / 125000000000) = -Real.log (125000000000 / 976321585903) := by
    rw [show ((976321585903 / 125000000000) : ℝ) = ((125000000000 / 976321585903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13838_neg : (207047287 / 100000000) ≤ -Real.log (250000000000 / 1982142857143) ∧
    -Real.log (250000000000 / 1982142857143) ≤ (2070472873 / 1000000000) := by
  have h := checkLog_sound (w := (982142857143 / 2982142857143)) (n := 12)
    (lo := (68417851 / 100000000)) (hi := (684178511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982142857143 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1982142857143 / 1000000000000) = 1/(250000000000 / 1982142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13838 : Bounds (207047287 / 100000000) (2070472873 / 1000000000) (Real.log (1982142857143 / 250000000000)) := by
  have h := reflection_log_13838_neg
  have he : Real.log (1982142857143 / 250000000000) = -Real.log (250000000000 / 1982142857143) := by
    rw [show ((1982142857143 / 250000000000) : ℝ) = ((250000000000 / 1982142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13839_neg : (36003213 / 62500000) ≤ -Real.log (1000 / 1779) ∧
    -Real.log (1000 / 1779) ≤ (576051409 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 2779)) (n := 12)
    (lo := (36003213 / 62500000)) (hi := (576051409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1779 / 1000) = 1/(1000 / 1779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13839 : Bounds (36003213 / 62500000) (576051409 / 1000000000) (Real.log (1779 / 1000)) := by
  have h := reflection_log_13839_neg
  have he : Real.log (1779 / 1000) = -Real.log (1000 / 1779) := by
    rw [show ((1779 / 1000) : ℝ) = ((1000 / 1779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13840_neg : (2948423 / 1953125) ≤ -Real.log (221 / 1000) ∧
    -Real.log (221 / 1000) ≤ (1509592579 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 471)) (n := 12)
    (lo := (15412277 / 125000000)) (hi := (123298217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 221) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 221) = 1/(221 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13840 : Bounds (-1509592579 / 1000000000) (-2948423 / 1953125) (Real.log (221 / 1000)) := by
  have h := reflection_log_13840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13841_neg : (97337 / 125000000) ≤ -Real.log (1000000 / 1000779) ∧
    -Real.log (1000000 / 1000779) ≤ (778697 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 2000779)) (n := 12)
    (lo := (97337 / 125000000)) (hi := (778697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000779 / 1000000) = 1/(1000000 / 1000779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13841 : Bounds (97337 / 125000000) (778697 / 1000000000) (Real.log (1000779 / 1000000)) := by
  have h := reflection_log_13841_neg
  have he : Real.log (1000779 / 1000000) = -Real.log (1000000 / 1000779) := by
    rw [show ((1000779 / 1000000) : ℝ) = ((1000000 / 1000779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13842_neg : (779303 / 1000000000) ≤ -Real.log (999221 / 1000000) ∧
    -Real.log (999221 / 1000000) ≤ (97413 / 125000000) := by
  have h := checkLog_sound (w := (779 / 1999221)) (n := 12)
    (lo := (779303 / 1000000000)) (hi := (97413 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999221) = 1/(999221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13842 : Bounds (-97413 / 125000000) (-779303 / 1000000000) (Real.log (999221 / 1000000)) := by
  have h := reflection_log_13842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13843_neg : (364834761 / 1000000000) ≤ -Real.log (250000 / 360069) ∧
    -Real.log (250000 / 360069) ≤ (182417381 / 500000000) := by
  have h := checkLog_sound (w := (110069 / 610069)) (n := 12)
    (lo := (364834761 / 1000000000)) (hi := (182417381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360069 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360069 / 250000) = 1/(250000 / 360069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13843 : Bounds (364834761 / 1000000000) (182417381 / 500000000) (Real.log (360069 / 250000)) := by
  have h := reflection_log_13843_neg
  have he : Real.log (360069 / 250000) = -Real.log (250000 / 360069) := by
    rw [show ((360069 / 250000) : ℝ) = ((250000 / 360069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13844_neg : (580311473 / 1000000000) ≤ -Real.log (139931 / 250000) ∧
    -Real.log (139931 / 250000) ≤ (290155737 / 500000000) := by
  have h := checkLog_sound (w := (110069 / 389931)) (n := 12)
    (lo := (580311473 / 1000000000)) (hi := (290155737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 139931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 139931) = 1/(139931 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13844 : Bounds (-290155737 / 500000000) (-580311473 / 1000000000) (Real.log (139931 / 250000)) := by
  have h := reflection_log_13844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13845_neg : (14673517 / 40000000) ≤ -Real.log (250000 / 360791) ∧
    -Real.log (250000 / 360791) ≤ (183418963 / 500000000) := by
  have h := checkLog_sound (w := (110791 / 610791)) (n := 12)
    (lo := (14673517 / 40000000)) (hi := (183418963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360791 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360791 / 250000) = 1/(250000 / 360791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13845 : Bounds (14673517 / 40000000) (183418963 / 500000000) (Real.log (360791 / 250000)) := by
  have h := reflection_log_13845_neg
  have he : Real.log (360791 / 250000) = -Real.log (250000 / 360791) := by
    rw [show ((360791 / 250000) : ℝ) = ((250000 / 360791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13846_neg : (146371129 / 250000000) ≤ -Real.log (139209 / 250000) ∧
    -Real.log (139209 / 250000) ≤ (585484517 / 1000000000) := by
  have h := checkLog_sound (w := (110791 / 389209)) (n := 12)
    (lo := (146371129 / 250000000)) (hi := (585484517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 139209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 139209) = 1/(139209 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13846 : Bounds (-585484517 / 1000000000) (-146371129 / 250000000) (Real.log (139209 / 250000)) := by
  have h := reflection_log_13846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13847_neg : (218646591 / 1000000000) ≤ -Real.log (50225354319 / 62500000000) ∧
    -Real.log (50225354319 / 62500000000) ≤ (3416353 / 15625000) := by
  have h := checkLog_sound (w := (12274645681 / 112725354319)) (n := 12)
    (lo := (218646591 / 1000000000)) (hi := (3416353 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 50225354319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 50225354319) = 1/(50225354319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13847 : Bounds (-3416353 / 15625000) (-218646591 / 1000000000) (Real.log (50225354319 / 62500000000)) := by
  have h := reflection_log_13847_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13848_neg : (26934589 / 125000000) ≤ -Real.log (50384815239 / 62500000000) ∧
    -Real.log (50384815239 / 62500000000) ≤ (215476713 / 1000000000) := by
  have h := checkLog_sound (w := (12115184761 / 112884815239)) (n := 12)
    (lo := (26934589 / 125000000)) (hi := (215476713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 50384815239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 50384815239) = 1/(50384815239 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13848 : Bounds (-215476713 / 1000000000) (-26934589 / 125000000) (Real.log (50384815239 / 62500000000)) := by
  have h := reflection_log_13848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13849_neg : (189029247 / 200000000) ≤ -Real.log (500000000000 / 1286594821733) ∧
    -Real.log (500000000000 / 1286594821733) ≤ (945146237 / 1000000000) := by
  have h := checkLog_sound (w := (286594821733 / 2286594821733)) (n := 12)
    (lo := (50399811 / 200000000)) (hi := (15749941 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286594821733 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1286594821733 / 1000000000000) = 1/(500000000000 / 1286594821733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13849 : Bounds (189029247 / 200000000) (945146237 / 1000000000) (Real.log (1286594821733 / 500000000000)) := by
  have h := reflection_log_13849_neg
  have he : Real.log (1286594821733 / 500000000000) = -Real.log (500000000000 / 1286594821733) := by
    rw [show ((1286594821733 / 500000000000) : ℝ) = ((500000000000 / 1286594821733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13850_neg : (952322441 / 1000000000) ≤ -Real.log (500000000000 / 1295860899799) ∧
    -Real.log (500000000000 / 1295860899799) ≤ (952322443 / 1000000000) := by
  have h := checkLog_sound (w := (295860899799 / 2295860899799)) (n := 12)
    (lo := (259175261 / 1000000000)) (hi := (129587631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295860899799 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1295860899799 / 1000000000000) = 1/(500000000000 / 1295860899799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13850 : Bounds (952322441 / 1000000000) (952322443 / 1000000000) (Real.log (1295860899799 / 500000000000)) := by
  have h := reflection_log_13850_neg
  have he : Real.log (1295860899799 / 500000000000) = -Real.log (500000000000 / 1295860899799) := by
    rw [show ((1295860899799 / 500000000000) : ℝ) = ((500000000000 / 1295860899799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13851_neg : (207047287 / 100000000) ≤ -Real.log (100000000000 / 792857142857) ∧
    -Real.log (100000000000 / 792857142857) ≤ (2070472873 / 1000000000) := by
  have h := checkLog_sound (w := (392857142857 / 1192857142857)) (n := 12)
    (lo := (68417851 / 100000000)) (hi := (684178511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792857142857 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(792857142857 / 400000000000) = 1/(100000000000 / 792857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13851 : Bounds (207047287 / 100000000) (2070472873 / 1000000000) (Real.log (792857142857 / 100000000000)) := by
  have h := reflection_log_13851_neg
  have he : Real.log (792857142857 / 100000000000) = -Real.log (100000000000 / 792857142857) := by
    rw [show ((792857142857 / 100000000000) : ℝ) = ((100000000000 / 792857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13852_neg : (130352749 / 62500000) ≤ -Real.log (500000000000 / 4024886877829) ∧
    -Real.log (500000000000 / 4024886877829) ≤ (521410997 / 250000000) := by
  have h := checkLog_sound (w := (24886877829 / 8024886877829)) (n := 12)
    (lo := (1550611 / 250000000)) (hi := (1240489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4024886877829 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4024886877829 / 4000000000000) = 1/(500000000000 / 4024886877829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13852 : Bounds (130352749 / 62500000) (521410997 / 250000000) (Real.log (4024886877829 / 500000000000)) := by
  have h := reflection_log_13852_neg
  have he : Real.log (4024886877829 / 500000000000) = -Real.log (500000000000 / 4024886877829) := by
    rw [show ((4024886877829 / 500000000000) : ℝ) = ((500000000000 / 4024886877829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13853_neg : (577736329 / 1000000000) ≤ -Real.log (500 / 891) ∧
    -Real.log (500 / 891) ≤ (57773633 / 100000000) := by
  have h := checkLog_sound (w := (391 / 1391)) (n := 12)
    (lo := (577736329 / 1000000000)) (hi := (57773633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891 / 500) = 1/(500 / 891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13853 : Bounds (577736329 / 1000000000) (57773633 / 100000000) (Real.log (891 / 500)) := by
  have h := reflection_log_13853_neg
  have he : Real.log (891 / 500) = -Real.log (500 / 891) := by
    rw [show ((891 / 500) : ℝ) = ((500 / 891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13854_neg : (304652043 / 200000000) ≤ -Real.log (109 / 500) ∧
    -Real.log (109 / 500) ≤ (761630109 / 500000000) := by
  have h := checkLog_sound (w := (8 / 117)) (n := 12)
    (lo := (27393171 / 200000000)) (hi := (4280183 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 109) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 109) = 1/(109 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13854 : Bounds (-761630109 / 500000000) (-304652043 / 200000000) (Real.log (109 / 500)) := by
  have h := reflection_log_13854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13855_neg : (390847 / 500000000) ≤ -Real.log (500000 / 500391) ∧
    -Real.log (500000 / 500391) ≤ (156339 / 200000000) := by
  have h := checkLog_sound (w := (391 / 1000391)) (n := 12)
    (lo := (390847 / 500000000)) (hi := (156339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500391 / 500000) = 1/(500000 / 500391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13855 : Bounds (390847 / 500000000) (156339 / 200000000) (Real.log (500391 / 500000)) := by
  have h := reflection_log_13855_neg
  have he : Real.log (500391 / 500000) = -Real.log (500000 / 500391) := by
    rw [show ((500391 / 500000) : ℝ) = ((500000 / 500391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13856_neg : (156461 / 200000000) ≤ -Real.log (499609 / 500000) ∧
    -Real.log (499609 / 500000) ≤ (391153 / 500000000) := by
  have h := checkLog_sound (w := (391 / 999609)) (n := 12)
    (lo := (156461 / 200000000)) (hi := (391153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499609) = 1/(499609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13856 : Bounds (-391153 / 500000000) (-156461 / 200000000) (Real.log (499609 / 500000)) := by
  have h := reflection_log_13856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13857_neg : (366384651 / 1000000000) ≤ -Real.log (100000 / 144251) ∧
    -Real.log (100000 / 144251) ≤ (91596163 / 250000000) := by
  have h := checkLog_sound (w := (44251 / 244251)) (n := 12)
    (lo := (366384651 / 1000000000)) (hi := (91596163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144251 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144251 / 100000) = 1/(100000 / 144251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13857 : Bounds (366384651 / 1000000000) (91596163 / 250000000) (Real.log (144251 / 100000)) := by
  have h := reflection_log_13857_neg
  have he : Real.log (144251 / 100000) = -Real.log (100000 / 144251) := by
    rw [show ((144251 / 100000) : ℝ) = ((100000 / 144251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13858_neg : (584310713 / 1000000000) ≤ -Real.log (55749 / 100000) ∧
    -Real.log (55749 / 100000) ≤ (292155357 / 500000000) := by
  have h := checkLog_sound (w := (44251 / 155749)) (n := 12)
    (lo := (584310713 / 1000000000)) (hi := (292155357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 55749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 55749) = 1/(55749 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13858 : Bounds (-292155357 / 500000000) (-584310713 / 1000000000) (Real.log (55749 / 100000)) := by
  have h := reflection_log_13858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13859_neg : (184195817 / 500000000) ≤ -Real.log (31250 / 45169) ∧
    -Real.log (31250 / 45169) ≤ (73678327 / 200000000) := by
  have h := checkLog_sound (w := (13919 / 76419)) (n := 12)
    (lo := (184195817 / 500000000)) (hi := (73678327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45169 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45169 / 31250) = 1/(31250 / 45169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13859 : Bounds (184195817 / 500000000) (73678327 / 200000000) (Real.log (45169 / 31250)) := by
  have h := reflection_log_13859_neg
  have he : Real.log (45169 / 31250) = -Real.log (31250 / 45169) := by
    rw [show ((45169 / 31250) : ℝ) = ((31250 / 45169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13860_neg : (58952257 / 100000000) ≤ -Real.log (17331 / 31250) ∧
    -Real.log (17331 / 31250) ≤ (589522571 / 1000000000) := by
  have h := checkLog_sound (w := (13919 / 48581)) (n := 12)
    (lo := (58952257 / 100000000)) (hi := (589522571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 17331) = 1/(17331 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13860 : Bounds (-589522571 / 1000000000) (-58952257 / 100000000) (Real.log (17331 / 31250)) := by
  have h := reflection_log_13860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13861_neg : (27641367 / 125000000) ≤ -Real.log (782823939 / 976562500) ∧
    -Real.log (782823939 / 976562500) ≤ (221130937 / 1000000000) := by
  have h := checkLog_sound (w := (193738561 / 1759386439)) (n := 12)
    (lo := (27641367 / 125000000)) (hi := (221130937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 782823939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 782823939) = 1/(782823939 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13861 : Bounds (-221130937 / 1000000000) (-27641367 / 125000000) (Real.log (782823939 / 976562500)) := by
  have h := reflection_log_13861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13862_neg : (217926061 / 1000000000) ≤ -Real.log (8041848999 / 10000000000) ∧
    -Real.log (8041848999 / 10000000000) ≤ (108963031 / 500000000) := by
  have h := checkLog_sound (w := (1958151001 / 18041848999)) (n := 12)
    (lo := (217926061 / 1000000000)) (hi := (108963031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 8041848999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 8041848999) = 1/(8041848999 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13862 : Bounds (-108963031 / 500000000) (-217926061 / 1000000000) (Real.log (8041848999 / 10000000000)) := by
  have h := reflection_log_13862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13863_neg : (237673841 / 250000000) ≤ -Real.log (62500000000 / 161719268507) ∧
    -Real.log (62500000000 / 161719268507) ≤ (475347683 / 500000000) := by
  have h := checkLog_sound (w := (36719268507 / 286719268507)) (n := 12)
    (lo := (32193523 / 125000000)) (hi := (51509637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161719268507 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(161719268507 / 125000000000) = 1/(62500000000 / 161719268507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13863 : Bounds (237673841 / 250000000) (475347683 / 500000000) (Real.log (161719268507 / 62500000000)) := by
  have h := reflection_log_13863_neg
  have he : Real.log (161719268507 / 62500000000) = -Real.log (62500000000 / 161719268507) := by
    rw [show ((161719268507 / 62500000000) : ℝ) = ((62500000000 / 161719268507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13864_neg : (239478551 / 250000000) ≤ -Real.log (250000000000 / 651563672033) ∧
    -Real.log (250000000000 / 651563672033) ≤ (478957103 / 500000000) := by
  have h := checkLog_sound (w := (151563672033 / 1151563672033)) (n := 12)
    (lo := (16547939 / 62500000)) (hi := (10590681 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651563672033 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(651563672033 / 500000000000) = 1/(250000000000 / 651563672033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13864 : Bounds (239478551 / 250000000) (478957103 / 500000000) (Real.log (651563672033 / 250000000000)) := by
  have h := reflection_log_13864_neg
  have he : Real.log (651563672033 / 250000000000) = -Real.log (250000000000 / 651563672033) := by
    rw [show ((651563672033 / 250000000000) : ℝ) = ((250000000000 / 651563672033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13865_neg : (130352749 / 62500000) ≤ -Real.log (125000000000 / 1006221719457) ∧
    -Real.log (125000000000 / 1006221719457) ≤ (521410997 / 250000000) := by
  have h := checkLog_sound (w := (6221719457 / 2006221719457)) (n := 12)
    (lo := (1550611 / 250000000)) (hi := (1240489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1006221719457 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1006221719457 / 1000000000000) = 1/(125000000000 / 1006221719457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13865 : Bounds (130352749 / 62500000) (521410997 / 250000000) (Real.log (1006221719457 / 125000000000)) := by
  have h := reflection_log_13865_neg
  have he : Real.log (1006221719457 / 125000000000) = -Real.log (125000000000 / 1006221719457) := by
    rw [show ((1006221719457 / 125000000000) : ℝ) = ((125000000000 / 1006221719457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13866_neg : (2100996543 / 1000000000) ≤ -Real.log (500000000000 / 4087155963303) ∧
    -Real.log (500000000000 / 4087155963303) ≤ (2100996547 / 1000000000) := by
  have h := checkLog_sound (w := (87155963303 / 8087155963303)) (n := 12)
    (lo := (21555003 / 1000000000)) (hi := (5388751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4087155963303 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4087155963303 / 4000000000000) = 1/(500000000000 / 4087155963303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13866 : Bounds (2100996543 / 1000000000) (2100996547 / 1000000000) (Real.log (4087155963303 / 500000000000)) := by
  have h := reflection_log_13866_neg
  have he : Real.log (4087155963303 / 500000000000) = -Real.log (500000000000 / 4087155963303) := by
    rw [show ((4087155963303 / 500000000000) : ℝ) = ((500000000000 / 4087155963303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13867_neg : (115883683 / 200000000) ≤ -Real.log (200 / 357) ∧
    -Real.log (200 / 357) ≤ (36213651 / 62500000) := by
  have h := checkLog_sound (w := (157 / 557)) (n := 12)
    (lo := (115883683 / 200000000)) (hi := (36213651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357 / 200) = 1/(200 / 357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13867 : Bounds (115883683 / 200000000) (36213651 / 62500000) (Real.log (357 / 200)) := by
  have h := reflection_log_13867_neg
  have he : Real.log (357 / 200) = -Real.log (200 / 357) := by
    rw [show ((357 / 200) : ℝ) = ((200 / 357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13868_neg : (1537117249 / 1000000000) ≤ -Real.log (43 / 200) ∧
    -Real.log (43 / 200) ≤ (384279313 / 250000000) := by
  have h := checkLog_sound (w := (7 / 93)) (n := 12)
    (lo := (150822889 / 1000000000)) (hi := (15082289 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 43) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50 / 43) = 1/(43 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13868 : Bounds (-384279313 / 250000000) (-1537117249 / 1000000000) (Real.log (43 / 200)) := by
  have h := reflection_log_13868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13869_neg : (196173 / 250000000) ≤ -Real.log (200000 / 200157) ∧
    -Real.log (200000 / 200157) ≤ (784693 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 400157)) (n := 12)
    (lo := (196173 / 250000000)) (hi := (784693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200157 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200157 / 200000) = 1/(200000 / 200157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13869 : Bounds (196173 / 250000000) (784693 / 1000000000) (Real.log (200157 / 200000)) := by
  have h := reflection_log_13869_neg
  have he : Real.log (200157 / 200000) = -Real.log (200000 / 200157) := by
    rw [show ((200157 / 200000) : ℝ) = ((200000 / 200157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13870_neg : (196327 / 250000000) ≤ -Real.log (199843 / 200000) ∧
    -Real.log (199843 / 200000) ≤ (785309 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 399843)) (n := 12)
    (lo := (196327 / 250000000)) (hi := (785309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199843) = 1/(199843 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13870 : Bounds (-785309 / 1000000000) (-196327 / 250000000) (Real.log (199843 / 200000)) := by
  have h := reflection_log_13870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13871_neg : (91984593 / 250000000) ≤ -Real.log (1000000 / 1444753) ∧
    -Real.log (1000000 / 1444753) ≤ (367938373 / 1000000000) := by
  have h := checkLog_sound (w := (444753 / 2444753)) (n := 12)
    (lo := (91984593 / 250000000)) (hi := (367938373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1444753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1444753 / 1000000) = 1/(1000000 / 1444753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13871 : Bounds (91984593 / 250000000) (367938373 / 1000000000) (Real.log (1444753 / 1000000)) := by
  have h := reflection_log_13871_neg
  have he : Real.log (1444753 / 1000000) = -Real.log (1000000 / 1444753) := by
    rw [show ((1444753 / 1000000) : ℝ) = ((1000000 / 1444753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13872_neg : (588342219 / 1000000000) ≤ -Real.log (555247 / 1000000) ∧
    -Real.log (555247 / 1000000) ≤ (29417111 / 50000000) := by
  have h := checkLog_sound (w := (444753 / 1555247)) (n := 12)
    (lo := (588342219 / 1000000000)) (hi := (29417111 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 555247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 555247) = 1/(555247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13872 : Bounds (-29417111 / 50000000) (-588342219 / 1000000000) (Real.log (555247 / 1000000)) := by
  have h := reflection_log_13872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13873_neg : (369949841 / 1000000000) ≤ -Real.log (500000 / 723831) ∧
    -Real.log (500000 / 723831) ≤ (184974921 / 500000000) := by
  have h := checkLog_sound (w := (223831 / 1223831)) (n := 12)
    (lo := (369949841 / 1000000000)) (hi := (184974921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723831 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723831 / 500000) = 1/(500000 / 723831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13873 : Bounds (369949841 / 1000000000) (184974921 / 500000000) (Real.log (723831 / 500000)) := by
  have h := reflection_log_13873_neg
  have he : Real.log (723831 / 500000) = -Real.log (500000 / 723831) := by
    rw [show ((723831 / 500000) : ℝ) = ((500000 / 723831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13874_neg : (593595101 / 1000000000) ≤ -Real.log (276169 / 500000) ∧
    -Real.log (276169 / 500000) ≤ (296797551 / 500000000) := by
  have h := checkLog_sound (w := (223831 / 776169)) (n := 12)
    (lo := (593595101 / 1000000000)) (hi := (296797551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 276169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 276169) = 1/(276169 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13874 : Bounds (-296797551 / 500000000) (-593595101 / 1000000000) (Real.log (276169 / 500000)) := by
  have h := reflection_log_13874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13875_neg : (223645259 / 1000000000) ≤ -Real.log (199899683439 / 250000000000) ∧
    -Real.log (199899683439 / 250000000000) ≤ (11182263 / 50000000) := by
  have h := checkLog_sound (w := (50100316561 / 449899683439)) (n := 12)
    (lo := (223645259 / 1000000000)) (hi := (11182263 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 199899683439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 199899683439) = 1/(199899683439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13875 : Bounds (-11182263 / 50000000) (-223645259 / 1000000000) (Real.log (199899683439 / 250000000000)) := by
  have h := reflection_log_13875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13876_neg : (110201923 / 500000000) ≤ -Real.log (802194768991 / 1000000000000) ∧
    -Real.log (802194768991 / 1000000000000) ≤ (220403847 / 1000000000) := by
  have h := checkLog_sound (w := (197805231009 / 1802194768991)) (n := 12)
    (lo := (110201923 / 500000000)) (hi := (220403847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 802194768991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 802194768991) = 1/(802194768991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13876 : Bounds (-220403847 / 1000000000) (-110201923 / 500000000) (Real.log (802194768991 / 1000000000000)) := by
  have h := reflection_log_13876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13877_neg : (956280591 / 1000000000) ≤ -Real.log (500000000000 / 1301000275553) ∧
    -Real.log (500000000000 / 1301000275553) ≤ (956280593 / 1000000000) := by
  have h := checkLog_sound (w := (301000275553 / 2301000275553)) (n := 12)
    (lo := (263133411 / 1000000000)) (hi := (65783353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301000275553 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1301000275553 / 1000000000000) = 1/(500000000000 / 1301000275553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13877 : Bounds (956280591 / 1000000000) (956280593 / 1000000000) (Real.log (1301000275553 / 500000000000)) := by
  have h := reflection_log_13877_neg
  have he : Real.log (1301000275553 / 500000000000) = -Real.log (500000000000 / 1301000275553) := by
    rw [show ((1301000275553 / 500000000000) : ℝ) = ((500000000000 / 1301000275553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13878_neg : (963544941 / 1000000000) ≤ -Real.log (10000000000 / 26209712169) ∧
    -Real.log (10000000000 / 26209712169) ≤ (963544943 / 1000000000) := by
  have h := checkLog_sound (w := (6209712169 / 46209712169)) (n := 12)
    (lo := (270397761 / 1000000000)) (hi := (135198881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26209712169 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(26209712169 / 20000000000) = 1/(10000000000 / 26209712169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13878 : Bounds (963544941 / 1000000000) (963544943 / 1000000000) (Real.log (26209712169 / 10000000000)) := by
  have h := reflection_log_13878_neg
  have he : Real.log (26209712169 / 10000000000) = -Real.log (10000000000 / 26209712169) := by
    rw [show ((26209712169 / 10000000000) : ℝ) = ((10000000000 / 26209712169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13879_neg : (2100996543 / 1000000000) ≤ -Real.log (250000000000 / 2043577981651) ∧
    -Real.log (250000000000 / 2043577981651) ≤ (2100996547 / 1000000000) := by
  have h := checkLog_sound (w := (43577981651 / 4043577981651)) (n := 12)
    (lo := (21555003 / 1000000000)) (hi := (5388751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2043577981651 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2043577981651 / 2000000000000) = 1/(250000000000 / 2043577981651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13879 : Bounds (2100996543 / 1000000000) (2100996547 / 1000000000) (Real.log (2043577981651 / 250000000000)) := by
  have h := reflection_log_13879_neg
  have he : Real.log (2043577981651 / 250000000000) = -Real.log (250000000000 / 2043577981651) := by
    rw [show ((2043577981651 / 250000000000) : ℝ) = ((250000000000 / 2043577981651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13880_neg : (132283479 / 62500000) ≤ -Real.log (250000000000 / 2075581395349) ∧
    -Real.log (250000000000 / 2075581395349) ≤ (529133917 / 250000000) := by
  have h := checkLog_sound (w := (75581395349 / 4075581395349)) (n := 12)
    (lo := (9273531 / 250000000)) (hi := (296753 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2075581395349 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2075581395349 / 2000000000000) = 1/(250000000000 / 2075581395349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13880 : Bounds (132283479 / 62500000) (529133917 / 250000000) (Real.log (2075581395349 / 250000000000)) := by
  have h := reflection_log_13880_neg
  have he : Real.log (2075581395349 / 250000000000) = -Real.log (250000000000 / 2075581395349) := by
    rw [show ((2075581395349 / 250000000000) : ℝ) = ((250000000000 / 2075581395349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13881_neg : (145274419 / 250000000) ≤ -Real.log (250 / 447) ∧
    -Real.log (250 / 447) ≤ (581097677 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 697)) (n := 12)
    (lo := (145274419 / 250000000)) (hi := (581097677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447 / 250) = 1/(250 / 447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13881 : Bounds (145274419 / 250000000) (581097677 / 1000000000) (Real.log (447 / 250)) := by
  have h := reflection_log_13881_neg
  have he : Real.log (447 / 250) = -Real.log (250 / 447) := by
    rw [show ((447 / 250) : ℝ) = ((250 / 447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13882_neg : (1551169003 / 1000000000) ≤ -Real.log (53 / 250) ∧
    -Real.log (53 / 250) ≤ (775584503 / 500000000) := by
  have h := checkLog_sound (w := (19 / 231)) (n := 12)
    (lo := (164874643 / 1000000000)) (hi := (41218661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 106) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 106) = 1/(53 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13882 : Bounds (-775584503 / 500000000) (-1551169003 / 1000000000) (Real.log (53 / 250)) := by
  have h := reflection_log_13882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13883_neg : (787689 / 1000000000) ≤ -Real.log (250000 / 250197) ∧
    -Real.log (250000 / 250197) ≤ (78769 / 100000000) := by
  have h := checkLog_sound (w := (197 / 500197)) (n := 12)
    (lo := (787689 / 1000000000)) (hi := (78769 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250197 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250197 / 250000) = 1/(250000 / 250197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13883 : Bounds (787689 / 1000000000) (78769 / 100000000) (Real.log (250197 / 250000)) := by
  have h := reflection_log_13883_neg
  have he : Real.log (250197 / 250000) = -Real.log (250000 / 250197) := by
    rw [show ((250197 / 250000) : ℝ) = ((250000 / 250197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13884_neg : (78831 / 100000000) ≤ -Real.log (249803 / 250000) ∧
    -Real.log (249803 / 250000) ≤ (788311 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 499803)) (n := 12)
    (lo := (78831 / 100000000)) (hi := (788311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249803) = 1/(249803 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13884 : Bounds (-788311 / 1000000000) (-78831 / 100000000) (Real.log (249803 / 250000)) := by
  have h := reflection_log_13884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13885_neg : (369495903 / 1000000000) ≤ -Real.log (200000 / 289401) ∧
    -Real.log (200000 / 289401) ≤ (11546747 / 31250000) := by
  have h := checkLog_sound (w := (89401 / 489401)) (n := 12)
    (lo := (369495903 / 1000000000)) (hi := (11546747 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289401 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289401 / 200000) = 1/(200000 / 289401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13885 : Bounds (369495903 / 1000000000) (11546747 / 31250000) (Real.log (289401 / 200000)) := by
  have h := reflection_log_13885_neg
  have he : Real.log (289401 / 200000) = -Real.log (200000 / 289401) := by
    rw [show ((289401 / 200000) : ℝ) = ((200000 / 289401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13886_neg : (592406319 / 1000000000) ≤ -Real.log (110599 / 200000) ∧
    -Real.log (110599 / 200000) ≤ (7405079 / 12500000) := by
  have h := checkLog_sound (w := (89401 / 310599)) (n := 12)
    (lo := (592406319 / 1000000000)) (hi := (7405079 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 110599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 110599) = 1/(110599 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13886 : Bounds (-7405079 / 12500000) (-592406319 / 1000000000) (Real.log (110599 / 200000)) := by
  have h := reflection_log_13886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13887_neg : (37151183 / 100000000) ≤ -Real.log (40000 / 57997) ∧
    -Real.log (40000 / 57997) ≤ (371511831 / 1000000000) := by
  have h := checkLog_sound (w := (17997 / 97997)) (n := 12)
    (lo := (37151183 / 100000000)) (hi := (371511831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57997 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57997 / 40000) = 1/(40000 / 57997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13887 : Bounds (37151183 / 100000000) (371511831 / 1000000000) (Real.log (57997 / 40000)) := by
  have h := reflection_log_13887_neg
  have he : Real.log (57997 / 40000) = -Real.log (40000 / 57997) := by
    rw [show ((57997 / 40000) : ℝ) = ((40000 / 57997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

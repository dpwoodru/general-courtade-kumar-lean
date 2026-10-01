import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_832_neg : (40889273 / 500000000) ≤ -Real.log (230369 / 250000) ∧
    -Real.log (230369 / 250000) ≤ (81778547 / 1000000000) := by
  have h := checkLog_sound (w := (19631 / 480369)) (n := 12)
    (lo := (40889273 / 500000000)) (hi := (81778547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230369) = 1/(230369 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_832 : Bounds (-81778547 / 1000000000) (-40889273 / 500000000) (Real.log (230369 / 250000)) := by
  have h := reflection_log_832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_833_neg : (3092553 / 500000000) ≤ -Real.log (62114623839 / 62500000000) ∧
    -Real.log (62114623839 / 62500000000) ≤ (6185107 / 1000000000) := by
  have h := checkLog_sound (w := (385376161 / 124614623839)) (n := 12)
    (lo := (3092553 / 500000000)) (hi := (6185107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62114623839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62114623839) = 1/(62114623839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_833 : Bounds (-6185107 / 1000000000) (-3092553 / 500000000) (Real.log (62114623839 / 62500000000)) := by
  have h := reflection_log_833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_834_neg : (6152439 / 1000000000) ≤ -Real.log (993866447511 / 1000000000000) ∧
    -Real.log (993866447511 / 1000000000000) ≤ (153811 / 25000000) := by
  have h := checkLog_sound (w := (6133552489 / 1993866447511)) (n := 12)
    (lo := (6152439 / 1000000000)) (hi := (153811 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993866447511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993866447511) = 1/(993866447511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_834 : Bounds (-153811 / 25000000) (-6152439 / 1000000000) (Real.log (993866447511 / 1000000000000)) := by
  have h := reflection_log_834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_835_neg : (4904857 / 31250000) ≤ -Real.log (500000000000 / 584971731061) ∧
    -Real.log (500000000000 / 584971731061) ≤ (6278217 / 40000000) := by
  have h := checkLog_sound (w := (84971731061 / 1084971731061)) (n := 12)
    (lo := (4904857 / 31250000)) (hi := (6278217 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584971731061 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584971731061 / 500000000000) = 1/(500000000000 / 584971731061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_835 : Bounds (4904857 / 31250000) (6278217 / 40000000) (Real.log (584971731061 / 500000000000)) := by
  have h := reflection_log_835_neg
  have he : Real.log (584971731061 / 500000000000) = -Real.log (500000000000 / 584971731061) := by
    rw [show ((584971731061 / 500000000000) : ℝ) = ((500000000000 / 584971731061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_836_neg : (78685993 / 500000000) ≤ -Real.log (250000000000 / 292607729339) ∧
    -Real.log (250000000000 / 292607729339) ≤ (157371987 / 1000000000) := by
  have h := checkLog_sound (w := (42607729339 / 542607729339)) (n := 12)
    (lo := (78685993 / 500000000)) (hi := (157371987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292607729339 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292607729339 / 250000000000) = 1/(250000000000 / 292607729339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_836 : Bounds (78685993 / 500000000) (157371987 / 1000000000) (Real.log (292607729339 / 250000000000)) := by
  have h := reflection_log_836_neg
  have he : Real.log (292607729339 / 250000000000) = -Real.log (250000000000 / 292607729339) := by
    rw [show ((292607729339 / 250000000000) : ℝ) = ((250000000000 / 292607729339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_837_neg : (157386773 / 500000000) ≤ -Real.log (500000000000 / 684974523047) ∧
    -Real.log (500000000000 / 684974523047) ≤ (314773547 / 1000000000) := by
  have h := checkLog_sound (w := (184974523047 / 1184974523047)) (n := 12)
    (lo := (157386773 / 500000000)) (hi := (314773547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684974523047 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684974523047 / 500000000000) = 1/(500000000000 / 684974523047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_837 : Bounds (157386773 / 500000000) (314773547 / 1000000000) (Real.log (684974523047 / 500000000000)) := by
  have h := reflection_log_837_neg
  have he : Real.log (684974523047 / 500000000000) = -Real.log (500000000000 / 684974523047) := by
    rw [show ((684974523047 / 500000000000) : ℝ) = ((500000000000 / 684974523047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_838_neg : (19686159 / 62500000) ≤ -Real.log (500000000000 / 685114956151) ∧
    -Real.log (500000000000 / 685114956151) ≤ (62995709 / 200000000) := by
  have h := checkLog_sound (w := (185114956151 / 1185114956151)) (n := 12)
    (lo := (19686159 / 62500000)) (hi := (62995709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685114956151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685114956151 / 500000000000) = 1/(500000000000 / 685114956151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_838 : Bounds (19686159 / 62500000) (62995709 / 200000000) (Real.log (685114956151 / 500000000000)) := by
  have h := reflection_log_838_neg
  have he : Real.log (685114956151 / 500000000000) = -Real.log (500000000000 / 685114956151) := by
    rw [show ((685114956151 / 500000000000) : ℝ) = ((500000000000 / 685114956151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_839_neg : (36306313 / 250000000) ≤ -Real.log (10000 / 11563) ∧
    -Real.log (10000 / 11563) ≤ (145225253 / 1000000000) := by
  have h := checkLog_sound (w := (1563 / 21563)) (n := 12)
    (lo := (36306313 / 250000000)) (hi := (145225253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11563 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11563 / 10000) = 1/(10000 / 11563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_839 : Bounds (36306313 / 250000000) (145225253 / 1000000000) (Real.log (11563 / 10000)) := by
  have h := reflection_log_839_neg
  have he : Real.log (11563 / 10000) = -Real.log (10000 / 11563) := by
    rw [show ((11563 / 10000) : ℝ) = ((10000 / 11563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_840_neg : (169958297 / 1000000000) ≤ -Real.log (8437 / 10000) ∧
    -Real.log (8437 / 10000) ≤ (84979149 / 500000000) := by
  have h := checkLog_sound (w := (1563 / 18437)) (n := 12)
    (lo := (169958297 / 1000000000)) (hi := (84979149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8437) = 1/(8437 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_840 : Bounds (-84979149 / 500000000) (-169958297 / 1000000000) (Real.log (8437 / 10000)) := by
  have h := reflection_log_840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_841_neg : (156287 / 1000000000) ≤ -Real.log (10000000 / 10001563) ∧
    -Real.log (10000000 / 10001563) ≤ (1221 / 7812500) := by
  have h := checkLog_sound (w := (1563 / 20001563)) (n := 12)
    (lo := (156287 / 1000000000)) (hi := (1221 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001563 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001563 / 10000000) = 1/(10000000 / 10001563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_841 : Bounds (156287 / 1000000000) (1221 / 7812500) (Real.log (10001563 / 10000000)) := by
  have h := reflection_log_841_neg
  have he : Real.log (10001563 / 10000000) = -Real.log (10000000 / 10001563) := by
    rw [show ((10001563 / 10000000) : ℝ) = ((10000000 / 10001563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_842_neg : (19539 / 125000000) ≤ -Real.log (9998437 / 10000000) ∧
    -Real.log (9998437 / 10000000) ≤ (156313 / 1000000000) := by
  have h := checkLog_sound (w := (1563 / 19998437)) (n := 12)
    (lo := (19539 / 125000000)) (hi := (156313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998437) = 1/(9998437 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_842 : Bounds (-156313 / 1000000000) (-19539 / 125000000) (Real.log (9998437 / 10000000)) := by
  have h := reflection_log_842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_843_neg : (75448787 / 1000000000) ≤ -Real.log (31250 / 33699) ∧
    -Real.log (31250 / 33699) ≤ (18862197 / 250000000) := by
  have h := checkLog_sound (w := (2449 / 64949)) (n := 12)
    (lo := (75448787 / 1000000000)) (hi := (18862197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33699 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33699 / 31250) = 1/(31250 / 33699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_843 : Bounds (75448787 / 1000000000) (18862197 / 250000000) (Real.log (33699 / 31250)) := by
  have h := reflection_log_843_neg
  have he : Real.log (33699 / 31250) = -Real.log (31250 / 33699) := by
    rw [show ((33699 / 31250) : ℝ) = ((31250 / 33699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_844_neg : (81609267 / 1000000000) ≤ -Real.log (28801 / 31250) ∧
    -Real.log (28801 / 31250) ≤ (20402317 / 250000000) := by
  have h := checkLog_sound (w := (2449 / 60051)) (n := 12)
    (lo := (81609267 / 1000000000)) (hi := (20402317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28801) = 1/(28801 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_844 : Bounds (-20402317 / 250000000) (-81609267 / 1000000000) (Real.log (28801 / 31250)) := by
  have h := reflection_log_844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_845_neg : (3025629 / 40000000) ≤ -Real.log (40000 / 43143) ∧
    -Real.log (40000 / 43143) ≤ (37820363 / 500000000) := by
  have h := checkLog_sound (w := (3143 / 83143)) (n := 12)
    (lo := (3025629 / 40000000)) (hi := (37820363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43143 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43143 / 40000) = 1/(40000 / 43143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_845 : Bounds (3025629 / 40000000) (37820363 / 500000000) (Real.log (43143 / 40000)) := by
  have h := reflection_log_845_neg
  have he : Real.log (43143 / 40000) = -Real.log (40000 / 43143) := by
    rw [show ((43143 / 40000) : ℝ) = ((40000 / 43143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_846_neg : (40916947 / 500000000) ≤ -Real.log (36857 / 40000) ∧
    -Real.log (36857 / 40000) ≤ (16366779 / 200000000) := by
  have h := checkLog_sound (w := (3143 / 76857)) (n := 12)
    (lo := (40916947 / 500000000)) (hi := (16366779 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36857) = 1/(36857 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_846 : Bounds (-16366779 / 200000000) (-40916947 / 500000000) (Real.log (36857 / 40000)) := by
  have h := reflection_log_846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_847_neg : (387073 / 62500000) ≤ -Real.log (1590121551 / 1600000000) ∧
    -Real.log (1590121551 / 1600000000) ≤ (6193169 / 1000000000) := by
  have h := checkLog_sound (w := (9878449 / 3190121551)) (n := 12)
    (lo := (387073 / 62500000)) (hi := (6193169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1590121551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1590121551) = 1/(1590121551 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_847 : Bounds (-6193169 / 1000000000) (-387073 / 62500000) (Real.log (1590121551 / 1600000000)) := by
  have h := reflection_log_847_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_848_neg : (38503 / 6250000) ≤ -Real.log (970564899 / 976562500) ∧
    -Real.log (970564899 / 976562500) ≤ (6160481 / 1000000000) := by
  have h := checkLog_sound (w := (5997601 / 1947127399)) (n := 12)
    (lo := (38503 / 6250000)) (hi := (6160481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 970564899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 970564899) = 1/(970564899 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_848 : Bounds (-6160481 / 1000000000) (-38503 / 6250000) (Real.log (970564899 / 976562500)) := by
  have h := reflection_log_848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_849_neg : (78529027 / 500000000) ≤ -Real.log (50000000000 / 58503176973) ∧
    -Real.log (50000000000 / 58503176973) ≤ (31411611 / 200000000) := by
  have h := checkLog_sound (w := (8503176973 / 108503176973)) (n := 12)
    (lo := (78529027 / 500000000)) (hi := (31411611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58503176973 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58503176973 / 50000000000) = 1/(50000000000 / 58503176973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_849 : Bounds (78529027 / 500000000) (31411611 / 200000000) (Real.log (58503176973 / 50000000000)) := by
  have h := reflection_log_849_neg
  have he : Real.log (58503176973 / 50000000000) = -Real.log (50000000000 / 58503176973) := by
    rw [show ((58503176973 / 50000000000) : ℝ) = ((50000000000 / 58503176973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_850_neg : (157474619 / 1000000000) ≤ -Real.log (125000000000 / 146318881081) ∧
    -Real.log (125000000000 / 146318881081) ≤ (7873731 / 50000000) := by
  have h := checkLog_sound (w := (21318881081 / 271318881081)) (n := 12)
    (lo := (157474619 / 1000000000)) (hi := (7873731 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146318881081 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146318881081 / 125000000000) = 1/(125000000000 / 146318881081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_850 : Bounds (157474619 / 1000000000) (7873731 / 50000000) (Real.log (146318881081 / 125000000000)) := by
  have h := reflection_log_850_neg
  have he : Real.log (146318881081 / 125000000000) = -Real.log (125000000000 / 146318881081) := by
    rw [show ((146318881081 / 125000000000) : ℝ) = ((125000000000 / 146318881081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_851_neg : (19686159 / 62500000) ≤ -Real.log (10000000000 / 13702299123) ∧
    -Real.log (10000000000 / 13702299123) ≤ (62995709 / 200000000) := by
  have h := checkLog_sound (w := (3702299123 / 23702299123)) (n := 12)
    (lo := (19686159 / 62500000)) (hi := (62995709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13702299123 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13702299123 / 10000000000) = 1/(10000000000 / 13702299123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_851 : Bounds (19686159 / 62500000) (62995709 / 200000000) (Real.log (13702299123 / 10000000000)) := by
  have h := reflection_log_851_neg
  have he : Real.log (13702299123 / 10000000000) = -Real.log (10000000000 / 13702299123) := by
    rw [show ((13702299123 / 10000000000) : ℝ) = ((10000000000 / 13702299123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_852_neg : (315183549 / 1000000000) ≤ -Real.log (31250000000 / 42828463909) ∧
    -Real.log (31250000000 / 42828463909) ≤ (6303671 / 20000000) := by
  have h := checkLog_sound (w := (11578463909 / 74078463909)) (n := 12)
    (lo := (315183549 / 1000000000)) (hi := (6303671 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42828463909 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42828463909 / 31250000000) = 1/(31250000000 / 42828463909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_852 : Bounds (315183549 / 1000000000) (6303671 / 20000000) (Real.log (42828463909 / 31250000000)) := by
  have h := reflection_log_852_neg
  have he : Real.log (42828463909 / 31250000000) = -Real.log (31250000000 / 42828463909) := by
    rw [show ((42828463909 / 31250000000) : ℝ) = ((31250000000 / 42828463909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_853_neg : (145311731 / 1000000000) ≤ -Real.log (2500 / 2891) ∧
    -Real.log (2500 / 2891) ≤ (36327933 / 250000000) := by
  have h := checkLog_sound (w := (391 / 5391)) (n := 12)
    (lo := (145311731 / 1000000000)) (hi := (36327933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2891 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2891 / 2500) = 1/(2500 / 2891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_853 : Bounds (145311731 / 1000000000) (36327933 / 250000000) (Real.log (2891 / 2500)) := by
  have h := reflection_log_853_neg
  have he : Real.log (2891 / 2500) = -Real.log (2500 / 2891) := by
    rw [show ((2891 / 2500) : ℝ) = ((2500 / 2891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_854_neg : (17007683 / 100000000) ≤ -Real.log (2109 / 2500) ∧
    -Real.log (2109 / 2500) ≤ (170076831 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 4609)) (n := 12)
    (lo := (17007683 / 100000000)) (hi := (170076831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2109) = 1/(2109 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_854 : Bounds (-170076831 / 1000000000) (-17007683 / 100000000) (Real.log (2109 / 2500)) := by
  have h := reflection_log_854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_855_neg : (156387 / 1000000000) ≤ -Real.log (2500000 / 2500391) ∧
    -Real.log (2500000 / 2500391) ≤ (39097 / 250000000) := by
  have h := checkLog_sound (w := (391 / 5000391)) (n := 12)
    (lo := (156387 / 1000000000)) (hi := (39097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500391 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500391 / 2500000) = 1/(2500000 / 2500391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_855 : Bounds (156387 / 1000000000) (39097 / 250000000) (Real.log (2500391 / 2500000)) := by
  have h := reflection_log_855_neg
  have he : Real.log (2500391 / 2500000) = -Real.log (2500000 / 2500391) := by
    rw [show ((2500391 / 2500000) : ℝ) = ((2500000 / 2500391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_856_neg : (39103 / 250000000) ≤ -Real.log (2499609 / 2500000) ∧
    -Real.log (2499609 / 2500000) ≤ (156413 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 4999609)) (n := 12)
    (lo := (39103 / 250000000)) (hi := (156413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499609) = 1/(2499609 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_856 : Bounds (-156413 / 1000000000) (-39103 / 250000000) (Real.log (2499609 / 2500000)) := by
  have h := reflection_log_856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_857_neg : (4718447 / 62500000) ≤ -Real.log (500000 / 539209) ∧
    -Real.log (500000 / 539209) ≤ (75495153 / 1000000000) := by
  have h := checkLog_sound (w := (39209 / 1039209)) (n := 12)
    (lo := (4718447 / 62500000)) (hi := (75495153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539209 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539209 / 500000) = 1/(500000 / 539209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_857 : Bounds (4718447 / 62500000) (75495153 / 1000000000) (Real.log (539209 / 500000)) := by
  have h := reflection_log_857_neg
  have he : Real.log (539209 / 500000) = -Real.log (500000 / 539209) := by
    rw [show ((539209 / 500000) : ℝ) = ((500000 / 539209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_858_neg : (510397 / 6250000) ≤ -Real.log (460791 / 500000) ∧
    -Real.log (460791 / 500000) ≤ (81663521 / 1000000000) := by
  have h := checkLog_sound (w := (39209 / 960791)) (n := 12)
    (lo := (510397 / 6250000)) (hi := (81663521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460791) = 1/(460791 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_858 : Bounds (-81663521 / 1000000000) (-510397 / 6250000) (Real.log (460791 / 500000)) := by
  have h := reflection_log_858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_859_neg : (9461001 / 125000000) ≤ -Real.log (500000 / 539313) ∧
    -Real.log (500000 / 539313) ≤ (75688009 / 1000000000) := by
  have h := checkLog_sound (w := (39313 / 1039313)) (n := 12)
    (lo := (9461001 / 125000000)) (hi := (75688009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539313 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539313 / 500000) = 1/(500000 / 539313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_859 : Bounds (9461001 / 125000000) (75688009 / 1000000000) (Real.log (539313 / 500000)) := by
  have h := reflection_log_859_neg
  have he : Real.log (539313 / 500000) = -Real.log (500000 / 539313) := by
    rw [show ((539313 / 500000) : ℝ) = ((500000 / 539313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_860_neg : (20472311 / 250000000) ≤ -Real.log (460687 / 500000) ∧
    -Real.log (460687 / 500000) ≤ (16377849 / 200000000) := by
  have h := checkLog_sound (w := (39313 / 960687)) (n := 12)
    (lo := (20472311 / 250000000)) (hi := (16377849 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460687) = 1/(460687 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_860 : Bounds (-16377849 / 200000000) (-20472311 / 250000000) (Real.log (460687 / 500000)) := by
  have h := reflection_log_860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_861_neg : (1240247 / 200000000) ≤ -Real.log (248454488031 / 250000000000) ∧
    -Real.log (248454488031 / 250000000000) ≤ (1550309 / 250000000) := by
  have h := checkLog_sound (w := (1545511969 / 498454488031)) (n := 12)
    (lo := (1240247 / 200000000)) (hi := (1550309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248454488031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248454488031) = 1/(248454488031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_861 : Bounds (-1550309 / 250000000) (-1240247 / 200000000) (Real.log (248454488031 / 250000000000)) := by
  have h := reflection_log_861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_862_neg : (385523 / 62500000) ≤ -Real.log (248462654319 / 250000000000) ∧
    -Real.log (248462654319 / 250000000000) ≤ (6168369 / 1000000000) := by
  have h := checkLog_sound (w := (1537345681 / 498462654319)) (n := 12)
    (lo := (385523 / 62500000)) (hi := (6168369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248462654319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248462654319) = 1/(248462654319 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_862 : Bounds (-6168369 / 1000000000) (-385523 / 62500000) (Real.log (248462654319 / 250000000000)) := by
  have h := reflection_log_862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_863_neg : (9822417 / 62500000) ≤ -Real.log (25000000000 / 29254531881) ∧
    -Real.log (25000000000 / 29254531881) ≤ (157158673 / 1000000000) := by
  have h := checkLog_sound (w := (4254531881 / 54254531881)) (n := 12)
    (lo := (9822417 / 62500000)) (hi := (157158673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29254531881 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29254531881 / 25000000000) = 1/(25000000000 / 29254531881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_863 : Bounds (9822417 / 62500000) (157158673 / 1000000000) (Real.log (29254531881 / 25000000000)) := by
  have h := reflection_log_863_neg
  have he : Real.log (29254531881 / 25000000000) = -Real.log (25000000000 / 29254531881) := by
    rw [show ((29254531881 / 25000000000) : ℝ) = ((25000000000 / 29254531881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_864_neg : (157577253 / 1000000000) ≤ -Real.log (25000000000 / 29266779831) ∧
    -Real.log (25000000000 / 29266779831) ≤ (78788627 / 500000000) := by
  have h := checkLog_sound (w := (4266779831 / 54266779831)) (n := 12)
    (lo := (157577253 / 1000000000)) (hi := (78788627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29266779831 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29266779831 / 25000000000) = 1/(25000000000 / 29266779831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_864 : Bounds (157577253 / 1000000000) (78788627 / 500000000) (Real.log (29266779831 / 25000000000)) := by
  have h := reflection_log_864_neg
  have he : Real.log (29266779831 / 25000000000) = -Real.log (25000000000 / 29266779831) := by
    rw [show ((29266779831 / 25000000000) : ℝ) = ((25000000000 / 29266779831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_865_neg : (315183549 / 1000000000) ≤ -Real.log (500000000000 / 685255422543) ∧
    -Real.log (500000000000 / 685255422543) ≤ (6303671 / 20000000) := by
  have h := checkLog_sound (w := (185255422543 / 1185255422543)) (n := 12)
    (lo := (315183549 / 1000000000)) (hi := (6303671 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685255422543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685255422543 / 500000000000) = 1/(500000000000 / 685255422543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_865 : Bounds (315183549 / 1000000000) (6303671 / 20000000) (Real.log (685255422543 / 500000000000)) := by
  have h := reflection_log_865_neg
  have he : Real.log (685255422543 / 500000000000) = -Real.log (500000000000 / 685255422543) := by
    rw [show ((685255422543 / 500000000000) : ℝ) = ((500000000000 / 685255422543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_866_neg : (315388561 / 1000000000) ≤ -Real.log (500000000000 / 685395922239) ∧
    -Real.log (500000000000 / 685395922239) ≤ (157694281 / 500000000) := by
  have h := checkLog_sound (w := (185395922239 / 1185395922239)) (n := 12)
    (lo := (315388561 / 1000000000)) (hi := (157694281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685395922239 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685395922239 / 500000000000) = 1/(500000000000 / 685395922239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_866 : Bounds (315388561 / 1000000000) (157694281 / 500000000) (Real.log (685395922239 / 500000000000)) := by
  have h := reflection_log_866_neg
  have he : Real.log (685395922239 / 500000000000) = -Real.log (500000000000 / 685395922239) := by
    rw [show ((685395922239 / 500000000000) : ℝ) = ((500000000000 / 685395922239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_867_neg : (72699101 / 500000000) ≤ -Real.log (2000 / 2313) ∧
    -Real.log (2000 / 2313) ≤ (145398203 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 4313)) (n := 12)
    (lo := (72699101 / 500000000)) (hi := (145398203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2313 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2313 / 2000) = 1/(2000 / 2313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_867 : Bounds (72699101 / 500000000) (145398203 / 1000000000) (Real.log (2313 / 2000)) := by
  have h := reflection_log_867_neg
  have he : Real.log (2313 / 2000) = -Real.log (2000 / 2313) := by
    rw [show ((2313 / 2000) : ℝ) = ((2000 / 2313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_868_neg : (10637211 / 62500000) ≤ -Real.log (1687 / 2000) ∧
    -Real.log (1687 / 2000) ≤ (170195377 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 3687)) (n := 12)
    (lo := (10637211 / 62500000)) (hi := (170195377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1687) = 1/(1687 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_868 : Bounds (-170195377 / 1000000000) (-10637211 / 62500000) (Real.log (1687 / 2000)) := by
  have h := reflection_log_868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_869_neg : (156487 / 1000000000) ≤ -Real.log (2000000 / 2000313) ∧
    -Real.log (2000000 / 2000313) ≤ (19561 / 125000000) := by
  have h := checkLog_sound (w := (313 / 4000313)) (n := 12)
    (lo := (156487 / 1000000000)) (hi := (19561 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000313 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000313 / 2000000) = 1/(2000000 / 2000313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_869 : Bounds (156487 / 1000000000) (19561 / 125000000) (Real.log (2000313 / 2000000)) := by
  have h := reflection_log_869_neg
  have he : Real.log (2000313 / 2000000) = -Real.log (2000000 / 2000313) := by
    rw [show ((2000313 / 2000000) : ℝ) = ((2000000 / 2000313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_870_neg : (4891 / 31250000) ≤ -Real.log (1999687 / 2000000) ∧
    -Real.log (1999687 / 2000000) ≤ (156513 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 3999687)) (n := 12)
    (lo := (4891 / 31250000)) (hi := (156513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999687) = 1/(1999687 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_870 : Bounds (-156513 / 1000000000) (-4891 / 31250000) (Real.log (1999687 / 2000000)) := by
  have h := reflection_log_870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_871_neg : (37771221 / 500000000) ≤ -Real.log (1000000 / 1078469) ∧
    -Real.log (1000000 / 1078469) ≤ (75542443 / 1000000000) := by
  have h := checkLog_sound (w := (78469 / 2078469)) (n := 12)
    (lo := (37771221 / 500000000)) (hi := (75542443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078469 / 1000000) = 1/(1000000 / 1078469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_871 : Bounds (37771221 / 500000000) (75542443 / 1000000000) (Real.log (1078469 / 1000000)) := by
  have h := reflection_log_871_neg
  have he : Real.log (1078469 / 1000000) = -Real.log (1000000 / 1078469) := by
    rw [show ((1078469 / 1000000) : ℝ) = ((1000000 / 1078469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_872_neg : (81718861 / 1000000000) ≤ -Real.log (921531 / 1000000) ∧
    -Real.log (921531 / 1000000) ≤ (40859431 / 500000000) := by
  have h := checkLog_sound (w := (78469 / 1921531)) (n := 12)
    (lo := (81718861 / 1000000000)) (hi := (40859431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921531) = 1/(921531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_872 : Bounds (-40859431 / 500000000) (-81718861 / 1000000000) (Real.log (921531 / 1000000)) := by
  have h := reflection_log_872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_873_neg : (7573529 / 100000000) ≤ -Real.log (1000000 / 1078677) ∧
    -Real.log (1000000 / 1078677) ≤ (75735291 / 1000000000) := by
  have h := checkLog_sound (w := (78677 / 2078677)) (n := 12)
    (lo := (7573529 / 100000000)) (hi := (75735291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078677 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078677 / 1000000) = 1/(1000000 / 1078677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_873 : Bounds (7573529 / 100000000) (75735291 / 1000000000) (Real.log (1078677 / 1000000)) := by
  have h := reflection_log_873_neg
  have he : Real.log (1078677 / 1000000) = -Real.log (1000000 / 1078677) := by
    rw [show ((1078677 / 1000000) : ℝ) = ((1000000 / 1078677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_874_neg : (40972299 / 500000000) ≤ -Real.log (921323 / 1000000) ∧
    -Real.log (921323 / 1000000) ≤ (81944599 / 1000000000) := by
  have h := checkLog_sound (w := (78677 / 1921323)) (n := 12)
    (lo := (40972299 / 500000000)) (hi := (81944599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921323) = 1/(921323 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_874 : Bounds (-81944599 / 1000000000) (-40972299 / 500000000) (Real.log (921323 / 1000000)) := by
  have h := reflection_log_874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_875_neg : (1552327 / 250000000) ≤ -Real.log (993809929671 / 1000000000000) ∧
    -Real.log (993809929671 / 1000000000000) ≤ (6209309 / 1000000000) := by
  have h := checkLog_sound (w := (6190070329 / 1993809929671)) (n := 12)
    (lo := (1552327 / 250000000)) (hi := (6209309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993809929671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993809929671) = 1/(993809929671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_875 : Bounds (-6209309 / 1000000000) (-1552327 / 250000000) (Real.log (993809929671 / 1000000000000)) := by
  have h := reflection_log_875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_876_neg : (3088209 / 500000000) ≤ -Real.log (993842616039 / 1000000000000) ∧
    -Real.log (993842616039 / 1000000000000) ≤ (6176419 / 1000000000) := by
  have h := checkLog_sound (w := (6157383961 / 1993842616039)) (n := 12)
    (lo := (3088209 / 500000000)) (hi := (6176419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993842616039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993842616039) = 1/(993842616039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_876 : Bounds (-6176419 / 1000000000) (-3088209 / 500000000) (Real.log (993842616039 / 1000000000000)) := by
  have h := reflection_log_876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_877_neg : (19657663 / 125000000) ≤ -Real.log (10000000000 / 11703013789) ∧
    -Real.log (10000000000 / 11703013789) ≤ (31452261 / 200000000) := by
  have h := checkLog_sound (w := (1703013789 / 21703013789)) (n := 12)
    (lo := (19657663 / 125000000)) (hi := (31452261 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11703013789 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11703013789 / 10000000000) = 1/(10000000000 / 11703013789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_877 : Bounds (19657663 / 125000000) (31452261 / 200000000) (Real.log (11703013789 / 10000000000)) := by
  have h := reflection_log_877_neg
  have he : Real.log (11703013789 / 10000000000) = -Real.log (10000000000 / 11703013789) := by
    rw [show ((11703013789 / 10000000000) : ℝ) = ((10000000000 / 11703013789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_878_neg : (9854993 / 62500000) ≤ -Real.log (500000000000 / 585395675567) ∧
    -Real.log (500000000000 / 585395675567) ≤ (157679889 / 1000000000) := by
  have h := checkLog_sound (w := (85395675567 / 1085395675567)) (n := 12)
    (lo := (9854993 / 62500000)) (hi := (157679889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585395675567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585395675567 / 500000000000) = 1/(500000000000 / 585395675567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_878 : Bounds (9854993 / 62500000) (157679889 / 1000000000) (Real.log (585395675567 / 500000000000)) := by
  have h := reflection_log_878_neg
  have he : Real.log (585395675567 / 500000000000) = -Real.log (500000000000 / 585395675567) := by
    rw [show ((585395675567 / 500000000000) : ℝ) = ((500000000000 / 585395675567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_879_neg : (315388561 / 1000000000) ≤ -Real.log (250000000000 / 342697961119) ∧
    -Real.log (250000000000 / 342697961119) ≤ (157694281 / 500000000) := by
  have h := checkLog_sound (w := (92697961119 / 592697961119)) (n := 12)
    (lo := (315388561 / 1000000000)) (hi := (157694281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342697961119 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342697961119 / 250000000000) = 1/(250000000000 / 342697961119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_879 : Bounds (315388561 / 1000000000) (157694281 / 500000000) (Real.log (342697961119 / 250000000000)) := by
  have h := reflection_log_879_neg
  have he : Real.log (342697961119 / 250000000000) = -Real.log (250000000000 / 342697961119) := by
    rw [show ((342697961119 / 250000000000) : ℝ) = ((250000000000 / 342697961119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_880_neg : (315593579 / 1000000000) ≤ -Real.log (250000000000 / 342768227623) ∧
    -Real.log (250000000000 / 342768227623) ≤ (15779679 / 50000000) := by
  have h := checkLog_sound (w := (92768227623 / 592768227623)) (n := 12)
    (lo := (315593579 / 1000000000)) (hi := (15779679 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342768227623 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342768227623 / 250000000000) = 1/(250000000000 / 342768227623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_880 : Bounds (315593579 / 1000000000) (15779679 / 50000000) (Real.log (342768227623 / 250000000000)) := by
  have h := reflection_log_880_neg
  have he : Real.log (342768227623 / 250000000000) = -Real.log (250000000000 / 342768227623) := by
    rw [show ((342768227623 / 250000000000) : ℝ) = ((250000000000 / 342768227623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_881_neg : (72742333 / 500000000) ≤ -Real.log (5000 / 5783) ∧
    -Real.log (5000 / 5783) ≤ (145484667 / 1000000000) := by
  have h := checkLog_sound (w := (783 / 10783)) (n := 12)
    (lo := (72742333 / 500000000)) (hi := (145484667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5783 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5783 / 5000) = 1/(5000 / 5783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_881 : Bounds (72742333 / 500000000) (145484667 / 1000000000) (Real.log (5783 / 5000)) := by
  have h := reflection_log_881_neg
  have he : Real.log (5783 / 5000) = -Real.log (5000 / 5783) := by
    rw [show ((5783 / 5000) : ℝ) = ((5000 / 5783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_882_neg : (170313937 / 1000000000) ≤ -Real.log (4217 / 5000) ∧
    -Real.log (4217 / 5000) ≤ (85156969 / 500000000) := by
  have h := checkLog_sound (w := (783 / 9217)) (n := 12)
    (lo := (170313937 / 1000000000)) (hi := (85156969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4217) = 1/(4217 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_882 : Bounds (-85156969 / 500000000) (-170313937 / 1000000000) (Real.log (4217 / 5000)) := by
  have h := reflection_log_882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_883_neg : (156587 / 1000000000) ≤ -Real.log (5000000 / 5000783) ∧
    -Real.log (5000000 / 5000783) ≤ (39147 / 250000000) := by
  have h := checkLog_sound (w := (783 / 10000783)) (n := 12)
    (lo := (156587 / 1000000000)) (hi := (39147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000783 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000783 / 5000000) = 1/(5000000 / 5000783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_883 : Bounds (156587 / 1000000000) (39147 / 250000000) (Real.log (5000783 / 5000000)) := by
  have h := reflection_log_883_neg
  have he : Real.log (5000783 / 5000000) = -Real.log (5000000 / 5000783) := by
    rw [show ((5000783 / 5000000) : ℝ) = ((5000000 / 5000783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_884_neg : (39153 / 250000000) ≤ -Real.log (4999217 / 5000000) ∧
    -Real.log (4999217 / 5000000) ≤ (156613 / 1000000000) := by
  have h := checkLog_sound (w := (783 / 9999217)) (n := 12)
    (lo := (39153 / 250000000)) (hi := (156613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999217) = 1/(4999217 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_884 : Bounds (-156613 / 1000000000) (-39153 / 250000000) (Real.log (4999217 / 5000000)) := by
  have h := reflection_log_884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_885_neg : (7558973 / 100000000) ≤ -Real.log (25000 / 26963) ∧
    -Real.log (25000 / 26963) ≤ (75589731 / 1000000000) := by
  have h := checkLog_sound (w := (1963 / 51963)) (n := 12)
    (lo := (7558973 / 100000000)) (hi := (75589731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26963 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26963 / 25000) = 1/(25000 / 26963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_885 : Bounds (7558973 / 100000000) (75589731 / 1000000000) (Real.log (26963 / 25000)) := by
  have h := reflection_log_885_neg
  have he : Real.log (26963 / 25000) = -Real.log (25000 / 26963) := by
    rw [show ((26963 / 25000) : ℝ) = ((25000 / 26963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_886_neg : (16354841 / 200000000) ≤ -Real.log (23037 / 25000) ∧
    -Real.log (23037 / 25000) ≤ (40887103 / 500000000) := by
  have h := checkLog_sound (w := (1963 / 48037)) (n := 12)
    (lo := (16354841 / 200000000)) (hi := (40887103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 23037) = 1/(23037 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_886 : Bounds (-40887103 / 500000000) (-16354841 / 200000000) (Real.log (23037 / 25000)) := by
  have h := reflection_log_886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_887_neg : (37890821 / 500000000) ≤ -Real.log (1000000 / 1078727) ∧
    -Real.log (1000000 / 1078727) ≤ (75781643 / 1000000000) := by
  have h := checkLog_sound (w := (78727 / 2078727)) (n := 12)
    (lo := (37890821 / 500000000)) (hi := (75781643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078727 / 1000000) = 1/(1000000 / 1078727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_887 : Bounds (37890821 / 500000000) (75781643 / 1000000000) (Real.log (1078727 / 1000000)) := by
  have h := reflection_log_887_neg
  have he : Real.log (1078727 / 1000000) = -Real.log (1000000 / 1078727) := by
    rw [show ((1078727 / 1000000) : ℝ) = ((1000000 / 1078727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_888_neg : (81998869 / 1000000000) ≤ -Real.log (921273 / 1000000) ∧
    -Real.log (921273 / 1000000) ≤ (8199887 / 100000000) := by
  have h := checkLog_sound (w := (78727 / 1921273)) (n := 12)
    (lo := (81998869 / 1000000000)) (hi := (8199887 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921273) = 1/(921273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_888 : Bounds (-8199887 / 100000000) (-81998869 / 1000000000) (Real.log (921273 / 1000000)) := by
  have h := reflection_log_888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_889_neg : (6217227 / 1000000000) ≤ -Real.log (993802059471 / 1000000000000) ∧
    -Real.log (993802059471 / 1000000000000) ≤ (1554307 / 250000000) := by
  have h := checkLog_sound (w := (6197940529 / 1993802059471)) (n := 12)
    (lo := (6217227 / 1000000000)) (hi := (1554307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993802059471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993802059471) = 1/(993802059471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_889 : Bounds (-1554307 / 250000000) (-6217227 / 1000000000) (Real.log (993802059471 / 1000000000000)) := by
  have h := reflection_log_889_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_890_neg : (3092237 / 500000000) ≤ -Real.log (621146631 / 625000000) ∧
    -Real.log (621146631 / 625000000) ≤ (247379 / 40000000) := by
  have h := checkLog_sound (w := (3853369 / 1246146631)) (n := 12)
    (lo := (3092237 / 500000000)) (hi := (247379 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 621146631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 621146631) = 1/(621146631 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_890 : Bounds (-247379 / 40000000) (-3092237 / 500000000) (Real.log (621146631 / 625000000)) := by
  have h := reflection_log_890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_891_neg : (4917623 / 31250000) ≤ -Real.log (500000000000 / 585210747927) ∧
    -Real.log (500000000000 / 585210747927) ≤ (157363937 / 1000000000) := by
  have h := checkLog_sound (w := (85210747927 / 1085210747927)) (n := 12)
    (lo := (4917623 / 31250000)) (hi := (157363937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585210747927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585210747927 / 500000000000) = 1/(500000000000 / 585210747927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_891 : Bounds (4917623 / 31250000) (157363937 / 1000000000) (Real.log (585210747927 / 500000000000)) := by
  have h := reflection_log_891_neg
  have he : Real.log (585210747927 / 500000000000) = -Real.log (500000000000 / 585210747927) := by
    rw [show ((585210747927 / 500000000000) : ℝ) = ((500000000000 / 585210747927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_892_neg : (157780511 / 1000000000) ≤ -Real.log (500000000000 / 585454582953) ∧
    -Real.log (500000000000 / 585454582953) ≤ (4930641 / 31250000) := by
  have h := checkLog_sound (w := (85454582953 / 1085454582953)) (n := 12)
    (lo := (157780511 / 1000000000)) (hi := (4930641 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585454582953 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585454582953 / 500000000000) = 1/(500000000000 / 585454582953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_892 : Bounds (157780511 / 1000000000) (4930641 / 31250000) (Real.log (585454582953 / 500000000000)) := by
  have h := reflection_log_892_neg
  have he : Real.log (585454582953 / 500000000000) = -Real.log (500000000000 / 585454582953) := by
    rw [show ((585454582953 / 500000000000) : ℝ) = ((500000000000 / 585454582953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_893_neg : (315593579 / 1000000000) ≤ -Real.log (100000000000 / 137107291049) ∧
    -Real.log (100000000000 / 137107291049) ≤ (15779679 / 50000000) := by
  have h := checkLog_sound (w := (37107291049 / 237107291049)) (n := 12)
    (lo := (315593579 / 1000000000)) (hi := (15779679 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137107291049 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137107291049 / 100000000000) = 1/(100000000000 / 137107291049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_893 : Bounds (315593579 / 1000000000) (15779679 / 50000000) (Real.log (137107291049 / 100000000000)) := by
  have h := reflection_log_893_neg
  have he : Real.log (137107291049 / 100000000000) = -Real.log (100000000000 / 137107291049) := by
    rw [show ((137107291049 / 100000000000) : ℝ) = ((100000000000 / 137107291049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_894_neg : (78949651 / 250000000) ≤ -Real.log (25000000000 / 34283851079) ∧
    -Real.log (25000000000 / 34283851079) ≤ (63159721 / 200000000) := by
  have h := checkLog_sound (w := (9283851079 / 59283851079)) (n := 12)
    (lo := (78949651 / 250000000)) (hi := (63159721 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34283851079 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34283851079 / 25000000000) = 1/(25000000000 / 34283851079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_894 : Bounds (78949651 / 250000000) (63159721 / 200000000) (Real.log (34283851079 / 25000000000)) := by
  have h := reflection_log_894_neg
  have he : Real.log (34283851079 / 25000000000) = -Real.log (25000000000 / 34283851079) := by
    rw [show ((34283851079 / 25000000000) : ℝ) = ((25000000000 / 34283851079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_895_neg : (145571123 / 1000000000) ≤ -Real.log (10000 / 11567) ∧
    -Real.log (10000 / 11567) ≤ (36392781 / 250000000) := by
  have h := checkLog_sound (w := (1567 / 21567)) (n := 12)
    (lo := (145571123 / 1000000000)) (hi := (36392781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11567 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11567 / 10000) = 1/(10000 / 11567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_895 : Bounds (145571123 / 1000000000) (36392781 / 250000000) (Real.log (11567 / 10000)) := by
  have h := reflection_log_895_neg
  have he : Real.log (11567 / 10000) = -Real.log (10000 / 11567) := by
    rw [show ((11567 / 10000) : ℝ) = ((10000 / 11567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

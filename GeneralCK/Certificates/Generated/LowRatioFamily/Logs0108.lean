import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6912_neg : (404423549 / 1000000000) ≤ -Real.log (62500000000 / 93652404747) ∧
    -Real.log (62500000000 / 93652404747) ≤ (8088471 / 20000000) := by
  have h := checkLog_sound (w := (31152404747 / 156152404747)) (n := 12)
    (lo := (404423549 / 1000000000)) (hi := (8088471 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93652404747 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93652404747 / 62500000000) = 1/(62500000000 / 93652404747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6912 : Bounds (404423549 / 1000000000) (8088471 / 20000000) (Real.log (93652404747 / 62500000000)) := by
  have h := reflection_log_6912_neg
  have he : Real.log (93652404747 / 62500000000) = -Real.log (62500000000 / 93652404747) := by
    rw [show ((93652404747 / 62500000000) : ℝ) = ((62500000000 / 93652404747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6913_neg : (101157961 / 250000000) ≤ -Real.log (62500000000 / 93671914043) ∧
    -Real.log (62500000000 / 93671914043) ≤ (80926369 / 200000000) := by
  have h := checkLog_sound (w := (31171914043 / 156171914043)) (n := 12)
    (lo := (101157961 / 250000000)) (hi := (80926369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93671914043 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93671914043 / 62500000000) = 1/(62500000000 / 93671914043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6913 : Bounds (101157961 / 250000000) (80926369 / 200000000) (Real.log (93671914043 / 62500000000)) := by
  have h := reflection_log_6913_neg
  have he : Real.log (93671914043 / 62500000000) = -Real.log (62500000000 / 93671914043) := by
    rw [show ((93671914043 / 62500000000) : ℝ) = ((62500000000 / 93671914043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6914_neg : (7282861 / 40000000) ≤ -Real.log (10000 / 11997) ∧
    -Real.log (10000 / 11997) ≤ (91035763 / 500000000) := by
  have h := checkLog_sound (w := (1997 / 21997)) (n := 12)
    (lo := (7282861 / 40000000)) (hi := (91035763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11997 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11997 / 10000) = 1/(10000 / 11997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6914 : Bounds (7282861 / 40000000) (91035763 / 500000000) (Real.log (11997 / 10000)) := by
  have h := reflection_log_6914_neg
  have he : Real.log (11997 / 10000) = -Real.log (10000 / 11997) := by
    rw [show ((11997 / 10000) : ℝ) = ((10000 / 11997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6915_neg : (222768621 / 1000000000) ≤ -Real.log (8003 / 10000) ∧
    -Real.log (8003 / 10000) ≤ (111384311 / 500000000) := by
  have h := checkLog_sound (w := (1997 / 18003)) (n := 12)
    (lo := (222768621 / 1000000000)) (hi := (111384311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8003) = 1/(8003 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6915 : Bounds (-111384311 / 500000000) (-222768621 / 1000000000) (Real.log (8003 / 10000)) := by
  have h := reflection_log_6915_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6916_neg : (78 / 390625) ≤ -Real.log (10000000 / 10001997) ∧
    -Real.log (10000000 / 10001997) ≤ (199681 / 1000000000) := by
  have h := checkLog_sound (w := (1997 / 20001997)) (n := 12)
    (lo := (78 / 390625)) (hi := (199681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001997 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001997 / 10000000) = 1/(10000000 / 10001997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6916 : Bounds (78 / 390625) (199681 / 1000000000) (Real.log (10001997 / 10000000)) := by
  have h := reflection_log_6916_neg
  have he : Real.log (10001997 / 10000000) = -Real.log (10000000 / 10001997) := by
    rw [show ((10001997 / 10000000) : ℝ) = ((10000000 / 10001997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6917_neg : (199719 / 1000000000) ≤ -Real.log (9998003 / 10000000) ∧
    -Real.log (9998003 / 10000000) ≤ (4993 / 25000000) := by
  have h := checkLog_sound (w := (1997 / 19998003)) (n := 12)
    (lo := (199719 / 1000000000)) (hi := (4993 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998003) = 1/(9998003 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6917 : Bounds (-4993 / 25000000) (-199719 / 1000000000) (Real.log (9998003 / 10000000)) := by
  have h := reflection_log_6917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6918_neg : (95697377 / 1000000000) ≤ -Real.log (500000 / 550213) ∧
    -Real.log (500000 / 550213) ≤ (47848689 / 500000000) := by
  have h := checkLog_sound (w := (50213 / 1050213)) (n := 12)
    (lo := (95697377 / 1000000000)) (hi := (47848689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550213 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550213 / 500000) = 1/(500000 / 550213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6918 : Bounds (95697377 / 1000000000) (47848689 / 500000000) (Real.log (550213 / 500000)) := by
  have h := reflection_log_6918_neg
  have he : Real.log (550213 / 500000) = -Real.log (500000 / 550213) := by
    rw [show ((550213 / 500000) : ℝ) = ((500000 / 550213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6919_neg : (105833961 / 1000000000) ≤ -Real.log (449787 / 500000) ∧
    -Real.log (449787 / 500000) ≤ (52916981 / 500000000) := by
  have h := checkLog_sound (w := (50213 / 949787)) (n := 12)
    (lo := (105833961 / 1000000000)) (hi := (52916981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449787) = 1/(449787 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6919 : Bounds (-52916981 / 500000000) (-105833961 / 1000000000) (Real.log (449787 / 500000)) := by
  have h := reflection_log_6919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6920_neg : (11990567 / 125000000) ≤ -Real.log (250000 / 275169) ∧
    -Real.log (250000 / 275169) ≤ (95924537 / 1000000000) := by
  have h := checkLog_sound (w := (25169 / 525169)) (n := 12)
    (lo := (11990567 / 125000000)) (hi := (95924537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275169 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(275169 / 250000) = 1/(250000 / 275169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6920 : Bounds (11990567 / 125000000) (95924537 / 1000000000) (Real.log (275169 / 250000)) := by
  have h := reflection_log_6920_neg
  have he : Real.log (275169 / 250000) = -Real.log (250000 / 275169) := by
    rw [show ((275169 / 250000) : ℝ) = ((250000 / 275169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6921_neg : (26527977 / 250000000) ≤ -Real.log (224831 / 250000) ∧
    -Real.log (224831 / 250000) ≤ (106111909 / 1000000000) := by
  have h := checkLog_sound (w := (25169 / 474831)) (n := 12)
    (lo := (26527977 / 250000000)) (hi := (106111909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 224831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 224831) = 1/(224831 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6921 : Bounds (-106111909 / 1000000000) (-26527977 / 250000000) (Real.log (224831 / 250000)) := by
  have h := reflection_log_6921_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6922_neg : (2546843 / 250000000) ≤ -Real.log (61866521439 / 62500000000) ∧
    -Real.log (61866521439 / 62500000000) ≤ (10187373 / 1000000000) := by
  have h := checkLog_sound (w := (633478561 / 124366521439)) (n := 12)
    (lo := (2546843 / 250000000)) (hi := (10187373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61866521439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61866521439) = 1/(61866521439 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6922 : Bounds (-10187373 / 1000000000) (-2546843 / 250000000) (Real.log (61866521439 / 62500000000)) := by
  have h := reflection_log_6922_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6923_neg : (10136583 / 1000000000) ≤ -Real.log (247478654631 / 250000000000) ∧
    -Real.log (247478654631 / 250000000000) ≤ (1267073 / 125000000) := by
  have h := checkLog_sound (w := (2521345369 / 497478654631)) (n := 12)
    (lo := (10136583 / 1000000000)) (hi := (1267073 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247478654631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247478654631) = 1/(247478654631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6923 : Bounds (-1267073 / 125000000) (-10136583 / 1000000000) (Real.log (247478654631 / 250000000000)) := by
  have h := reflection_log_6923_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6924_neg : (100765669 / 500000000) ≤ -Real.log (500000000000 / 611637286093) ∧
    -Real.log (500000000000 / 611637286093) ≤ (201531339 / 1000000000) := by
  have h := checkLog_sound (w := (111637286093 / 1111637286093)) (n := 12)
    (lo := (100765669 / 500000000)) (hi := (201531339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611637286093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611637286093 / 500000000000) = 1/(500000000000 / 611637286093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6924 : Bounds (100765669 / 500000000) (201531339 / 1000000000) (Real.log (611637286093 / 500000000000)) := by
  have h := reflection_log_6924_neg
  have he : Real.log (611637286093 / 500000000000) = -Real.log (500000000000 / 611637286093) := by
    rw [show ((611637286093 / 500000000000) : ℝ) = ((500000000000 / 611637286093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6925_neg : (40407289 / 200000000) ≤ -Real.log (500000000000 / 611946306337) ∧
    -Real.log (500000000000 / 611946306337) ≤ (101018223 / 500000000) := by
  have h := checkLog_sound (w := (111946306337 / 1111946306337)) (n := 12)
    (lo := (40407289 / 200000000)) (hi := (101018223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611946306337 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611946306337 / 500000000000) = 1/(500000000000 / 611946306337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6925 : Bounds (40407289 / 200000000) (101018223 / 500000000) (Real.log (611946306337 / 500000000000)) := by
  have h := reflection_log_6925_neg
  have he : Real.log (611946306337 / 500000000000) = -Real.log (500000000000 / 611946306337) := by
    rw [show ((611946306337 / 500000000000) : ℝ) = ((500000000000 / 611946306337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6926_neg : (101157961 / 250000000) ≤ -Real.log (500000000000 / 749375312343) ∧
    -Real.log (500000000000 / 749375312343) ≤ (80926369 / 200000000) := by
  have h := checkLog_sound (w := (249375312343 / 1249375312343)) (n := 12)
    (lo := (101157961 / 250000000)) (hi := (80926369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749375312343 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749375312343 / 500000000000) = 1/(500000000000 / 749375312343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6926 : Bounds (101157961 / 250000000) (80926369 / 200000000) (Real.log (749375312343 / 500000000000)) := by
  have h := reflection_log_6926_neg
  have he : Real.log (749375312343 / 500000000000) = -Real.log (500000000000 / 749375312343) := by
    rw [show ((749375312343 / 500000000000) : ℝ) = ((500000000000 / 749375312343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6927_neg : (404840147 / 1000000000) ≤ -Real.log (125000000000 / 187382856429) ∧
    -Real.log (125000000000 / 187382856429) ≤ (101210037 / 250000000) := by
  have h := checkLog_sound (w := (62382856429 / 312382856429)) (n := 12)
    (lo := (404840147 / 1000000000)) (hi := (101210037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187382856429 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187382856429 / 125000000000) = 1/(125000000000 / 187382856429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6927 : Bounds (404840147 / 1000000000) (101210037 / 250000000) (Real.log (187382856429 / 125000000000)) := by
  have h := reflection_log_6927_neg
  have he : Real.log (187382856429 / 125000000000) = -Real.log (125000000000 / 187382856429) := by
    rw [show ((187382856429 / 125000000000) : ℝ) = ((125000000000 / 187382856429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6928_neg : (45538719 / 250000000) ≤ -Real.log (5000 / 5999) ∧
    -Real.log (5000 / 5999) ≤ (182154877 / 1000000000) := by
  have h := checkLog_sound (w := (999 / 10999)) (n := 12)
    (lo := (45538719 / 250000000)) (hi := (182154877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5999 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5999 / 5000) = 1/(5000 / 5999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6928 : Bounds (45538719 / 250000000) (182154877 / 1000000000) (Real.log (5999 / 5000)) := by
  have h := reflection_log_6928_neg
  have he : Real.log (5999 / 5000) = -Real.log (5000 / 5999) := by
    rw [show ((5999 / 5000) : ℝ) = ((5000 / 5999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6929_neg : (111446791 / 500000000) ≤ -Real.log (4001 / 5000) ∧
    -Real.log (4001 / 5000) ≤ (222893583 / 1000000000) := by
  have h := checkLog_sound (w := (999 / 9001)) (n := 12)
    (lo := (111446791 / 500000000)) (hi := (222893583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4001) = 1/(4001 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6929 : Bounds (-222893583 / 1000000000) (-111446791 / 500000000) (Real.log (4001 / 5000)) := by
  have h := reflection_log_6929_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6930_neg : (9989 / 50000000) ≤ -Real.log (5000000 / 5000999) ∧
    -Real.log (5000000 / 5000999) ≤ (199781 / 1000000000) := by
  have h := checkLog_sound (w := (999 / 10000999)) (n := 12)
    (lo := (9989 / 50000000)) (hi := (199781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000999 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000999 / 5000000) = 1/(5000000 / 5000999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6930 : Bounds (9989 / 50000000) (199781 / 1000000000) (Real.log (5000999 / 5000000)) := by
  have h := reflection_log_6930_neg
  have he : Real.log (5000999 / 5000000) = -Real.log (5000000 / 5000999) := by
    rw [show ((5000999 / 5000000) : ℝ) = ((5000000 / 5000999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6931_neg : (199819 / 1000000000) ≤ -Real.log (4999001 / 5000000) ∧
    -Real.log (4999001 / 5000000) ≤ (9991 / 50000000) := by
  have h := checkLog_sound (w := (999 / 9999001)) (n := 12)
    (lo := (199819 / 1000000000)) (hi := (9991 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999001) = 1/(4999001 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6931 : Bounds (-9991 / 50000000) (-199819 / 1000000000) (Real.log (4999001 / 5000000)) := by
  have h := reflection_log_6931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6932_neg : (47871861 / 500000000) ≤ -Real.log (1000000 / 1100477) ∧
    -Real.log (1000000 / 1100477) ≤ (95743723 / 1000000000) := by
  have h := checkLog_sound (w := (100477 / 2100477)) (n := 12)
    (lo := (47871861 / 500000000)) (hi := (95743723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100477 / 1000000) = 1/(1000000 / 1100477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6932 : Bounds (47871861 / 500000000) (95743723 / 1000000000) (Real.log (1100477 / 1000000)) := by
  have h := reflection_log_6932_neg
  have he : Real.log (1100477 / 1000000) = -Real.log (1000000 / 1100477) := by
    rw [show ((1100477 / 1000000) : ℝ) = ((1000000 / 1100477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6933_neg : (3309083 / 31250000) ≤ -Real.log (899523 / 1000000) ∧
    -Real.log (899523 / 1000000) ≤ (105890657 / 1000000000) := by
  have h := checkLog_sound (w := (100477 / 1899523)) (n := 12)
    (lo := (3309083 / 31250000)) (hi := (105890657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899523) = 1/(899523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6933 : Bounds (-105890657 / 1000000000) (-3309083 / 31250000) (Real.log (899523 / 1000000)) := by
  have h := reflection_log_6933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6934_neg : (9597087 / 100000000) ≤ -Real.log (1000000 / 1100727) ∧
    -Real.log (1000000 / 1100727) ≤ (95970871 / 1000000000) := by
  have h := checkLog_sound (w := (100727 / 2100727)) (n := 12)
    (lo := (9597087 / 100000000)) (hi := (95970871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100727 / 1000000) = 1/(1000000 / 1100727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6934 : Bounds (9597087 / 100000000) (95970871 / 1000000000) (Real.log (1100727 / 1000000)) := by
  have h := reflection_log_6934_neg
  have he : Real.log (1100727 / 1000000) = -Real.log (1000000 / 1100727) := by
    rw [show ((1100727 / 1000000) : ℝ) = ((1000000 / 1100727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6935_neg : (106168619 / 1000000000) ≤ -Real.log (899273 / 1000000) ∧
    -Real.log (899273 / 1000000) ≤ (5308431 / 50000000) := by
  have h := checkLog_sound (w := (100727 / 1899273)) (n := 12)
    (lo := (106168619 / 1000000000)) (hi := (5308431 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899273) = 1/(899273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6935 : Bounds (-5308431 / 50000000) (-106168619 / 1000000000) (Real.log (899273 / 1000000)) := by
  have h := reflection_log_6935_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6936_neg : (10197749 / 1000000000) ≤ -Real.log (989854071471 / 1000000000000) ∧
    -Real.log (989854071471 / 1000000000000) ≤ (40791 / 4000000) := by
  have h := checkLog_sound (w := (10145928529 / 1989854071471)) (n := 12)
    (lo := (10197749 / 1000000000)) (hi := (40791 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989854071471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989854071471) = 1/(989854071471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6936 : Bounds (-40791 / 4000000) (-10197749 / 1000000000) (Real.log (989854071471 / 1000000000000)) := by
  have h := reflection_log_6936_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6937_neg : (10146933 / 1000000000) ≤ -Real.log (989904372471 / 1000000000000) ∧
    -Real.log (989904372471 / 1000000000000) ≤ (5073467 / 500000000) := by
  have h := checkLog_sound (w := (10095627529 / 1989904372471)) (n := 12)
    (lo := (10146933 / 1000000000)) (hi := (5073467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989904372471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989904372471) = 1/(989904372471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6937 : Bounds (-5073467 / 500000000) (-10146933 / 1000000000) (Real.log (989904372471 / 1000000000000)) := by
  have h := reflection_log_6937_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6938_neg : (100817189 / 500000000) ≤ -Real.log (125000000000 / 152925078069) ∧
    -Real.log (125000000000 / 152925078069) ≤ (201634379 / 1000000000) := by
  have h := checkLog_sound (w := (27925078069 / 277925078069)) (n := 12)
    (lo := (100817189 / 500000000)) (hi := (201634379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152925078069 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152925078069 / 125000000000) = 1/(125000000000 / 152925078069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6938 : Bounds (100817189 / 500000000) (201634379 / 1000000000) (Real.log (152925078069 / 125000000000)) := by
  have h := reflection_log_6938_neg
  have he : Real.log (152925078069 / 125000000000) = -Real.log (125000000000 / 152925078069) := by
    rw [show ((152925078069 / 125000000000) : ℝ) = ((125000000000 / 152925078069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6939_neg : (20213949 / 100000000) ≤ -Real.log (500000000000 / 612009367567) ∧
    -Real.log (500000000000 / 612009367567) ≤ (202139491 / 1000000000) := by
  have h := checkLog_sound (w := (112009367567 / 1112009367567)) (n := 12)
    (lo := (20213949 / 100000000)) (hi := (202139491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612009367567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612009367567 / 500000000000) = 1/(500000000000 / 612009367567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6939 : Bounds (20213949 / 100000000) (202139491 / 1000000000) (Real.log (612009367567 / 500000000000)) := by
  have h := reflection_log_6939_neg
  have he : Real.log (612009367567 / 500000000000) = -Real.log (500000000000 / 612009367567) := by
    rw [show ((612009367567 / 500000000000) : ℝ) = ((500000000000 / 612009367567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6940_neg : (404840147 / 1000000000) ≤ -Real.log (100000000000 / 149906285143) ∧
    -Real.log (100000000000 / 149906285143) ≤ (101210037 / 250000000) := by
  have h := checkLog_sound (w := (49906285143 / 249906285143)) (n := 12)
    (lo := (404840147 / 1000000000)) (hi := (101210037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149906285143 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149906285143 / 100000000000) = 1/(100000000000 / 149906285143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6940 : Bounds (404840147 / 1000000000) (101210037 / 250000000) (Real.log (149906285143 / 100000000000)) := by
  have h := reflection_log_6940_neg
  have he : Real.log (149906285143 / 100000000000) = -Real.log (100000000000 / 149906285143) := by
    rw [show ((149906285143 / 100000000000) : ℝ) = ((100000000000 / 149906285143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6941_neg : (202524229 / 500000000) ≤ -Real.log (250000000000 / 374843789053) ∧
    -Real.log (250000000000 / 374843789053) ≤ (405048459 / 1000000000) := by
  have h := checkLog_sound (w := (124843789053 / 624843789053)) (n := 12)
    (lo := (202524229 / 500000000)) (hi := (405048459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374843789053 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374843789053 / 250000000000) = 1/(250000000000 / 374843789053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6941 : Bounds (202524229 / 500000000) (405048459 / 1000000000) (Real.log (374843789053 / 250000000000)) := by
  have h := reflection_log_6941_neg
  have he : Real.log (374843789053 / 250000000000) = -Real.log (250000000000 / 374843789053) := by
    rw [show ((374843789053 / 250000000000) : ℝ) = ((250000000000 / 374843789053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6942_neg : (182238219 / 1000000000) ≤ -Real.log (10000 / 11999) ∧
    -Real.log (10000 / 11999) ≤ (9111911 / 50000000) := by
  have h := checkLog_sound (w := (1999 / 21999)) (n := 12)
    (lo := (182238219 / 1000000000)) (hi := (9111911 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11999 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11999 / 10000) = 1/(10000 / 11999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6942 : Bounds (182238219 / 1000000000) (9111911 / 50000000) (Real.log (11999 / 10000)) := by
  have h := reflection_log_6942_neg
  have he : Real.log (11999 / 10000) = -Real.log (10000 / 11999) := by
    rw [show ((11999 / 10000) : ℝ) = ((10000 / 11999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6943_neg : (223018559 / 1000000000) ≤ -Real.log (8001 / 10000) ∧
    -Real.log (8001 / 10000) ≤ (696933 / 3125000) := by
  have h := checkLog_sound (w := (1999 / 18001)) (n := 12)
    (lo := (223018559 / 1000000000)) (hi := (696933 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8001) = 1/(8001 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6943 : Bounds (-696933 / 3125000) (-223018559 / 1000000000) (Real.log (8001 / 10000)) := by
  have h := reflection_log_6943_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6944_neg : (4997 / 25000000) ≤ -Real.log (10000000 / 10001999) ∧
    -Real.log (10000000 / 10001999) ≤ (199881 / 1000000000) := by
  have h := checkLog_sound (w := (1999 / 20001999)) (n := 12)
    (lo := (4997 / 25000000)) (hi := (199881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001999 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001999 / 10000000) = 1/(10000000 / 10001999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6944 : Bounds (4997 / 25000000) (199881 / 1000000000) (Real.log (10001999 / 10000000)) := by
  have h := reflection_log_6944_neg
  have he : Real.log (10001999 / 10000000) = -Real.log (10000000 / 10001999) := by
    rw [show ((10001999 / 10000000) : ℝ) = ((10000000 / 10001999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6945_neg : (199919 / 1000000000) ≤ -Real.log (9998001 / 10000000) ∧
    -Real.log (9998001 / 10000000) ≤ (2499 / 12500000) := by
  have h := checkLog_sound (w := (1999 / 19998001)) (n := 12)
    (lo := (199919 / 1000000000)) (hi := (2499 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998001) = 1/(9998001 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6945 : Bounds (-2499 / 12500000) (-199919 / 1000000000) (Real.log (9998001 / 10000000)) := by
  have h := reflection_log_6945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6946_neg : (5986879 / 62500000) ≤ -Real.log (62500 / 68783) ∧
    -Real.log (62500 / 68783) ≤ (19158013 / 200000000) := by
  have h := checkLog_sound (w := (6283 / 131283)) (n := 12)
    (lo := (5986879 / 62500000)) (hi := (19158013 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68783 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68783 / 62500) = 1/(62500 / 68783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6946 : Bounds (5986879 / 62500000) (19158013 / 200000000) (Real.log (68783 / 62500)) := by
  have h := reflection_log_6946_neg
  have he : Real.log (68783 / 62500) = -Real.log (62500 / 68783) := by
    rw [show ((68783 / 62500) : ℝ) = ((62500 / 68783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6947_neg : (52973677 / 500000000) ≤ -Real.log (56217 / 62500) ∧
    -Real.log (56217 / 62500) ≤ (21189471 / 200000000) := by
  have h := checkLog_sound (w := (6283 / 118717)) (n := 12)
    (lo := (52973677 / 500000000)) (hi := (21189471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56217) = 1/(56217 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6947 : Bounds (-21189471 / 200000000) (-52973677 / 500000000) (Real.log (56217 / 62500)) := by
  have h := reflection_log_6947_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6948_neg : (9601811 / 100000000) ≤ -Real.log (1000000 / 1100779) ∧
    -Real.log (1000000 / 1100779) ≤ (96018111 / 1000000000) := by
  have h := checkLog_sound (w := (100779 / 2100779)) (n := 12)
    (lo := (9601811 / 100000000)) (hi := (96018111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100779 / 1000000) = 1/(1000000 / 1100779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6948 : Bounds (9601811 / 100000000) (96018111 / 1000000000) (Real.log (1100779 / 1000000)) := by
  have h := reflection_log_6948_neg
  have he : Real.log (1100779 / 1000000) = -Real.log (1000000 / 1100779) := by
    rw [show ((1100779 / 1000000) : ℝ) = ((1000000 / 1100779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6949_neg : (53113223 / 500000000) ≤ -Real.log (899221 / 1000000) ∧
    -Real.log (899221 / 1000000) ≤ (106226447 / 1000000000) := by
  have h := checkLog_sound (w := (100779 / 1899221)) (n := 12)
    (lo := (53113223 / 500000000)) (hi := (106226447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899221) = 1/(899221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6949 : Bounds (-106226447 / 1000000000) (-53113223 / 500000000) (Real.log (899221 / 1000000)) := by
  have h := reflection_log_6949_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6950_neg : (2041667 / 200000000) ≤ -Real.log (989843593159 / 1000000000000) ∧
    -Real.log (989843593159 / 1000000000000) ≤ (638021 / 62500000) := by
  have h := checkLog_sound (w := (10156406841 / 1989843593159)) (n := 12)
    (lo := (2041667 / 200000000)) (hi := (638021 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989843593159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989843593159) = 1/(989843593159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6950 : Bounds (-638021 / 62500000) (-2041667 / 200000000) (Real.log (989843593159 / 1000000000000)) := by
  have h := reflection_log_6950_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6951_neg : (10157289 / 1000000000) ≤ -Real.log (3866773911 / 3906250000) ∧
    -Real.log (3866773911 / 3906250000) ≤ (1015729 / 100000000) := by
  have h := checkLog_sound (w := (39476089 / 7773023911)) (n := 12)
    (lo := (10157289 / 1000000000)) (hi := (1015729 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3866773911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3866773911) = 1/(3866773911 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6951 : Bounds (-1015729 / 100000000) (-10157289 / 1000000000) (Real.log (3866773911 / 3906250000)) := by
  have h := reflection_log_6951_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6952_neg : (201737419 / 1000000000) ≤ -Real.log (500000000000 / 611763345607) ∧
    -Real.log (500000000000 / 611763345607) ≤ (10086871 / 50000000) := by
  have h := checkLog_sound (w := (111763345607 / 1111763345607)) (n := 12)
    (lo := (201737419 / 1000000000)) (hi := (10086871 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611763345607 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611763345607 / 500000000000) = 1/(500000000000 / 611763345607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6952 : Bounds (201737419 / 1000000000) (10086871 / 50000000) (Real.log (611763345607 / 500000000000)) := by
  have h := reflection_log_6952_neg
  have he : Real.log (611763345607 / 500000000000) = -Real.log (500000000000 / 611763345607) := by
    rw [show ((611763345607 / 500000000000) : ℝ) = ((500000000000 / 611763345607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6953_neg : (202244557 / 1000000000) ≤ -Real.log (500000000000 / 612073672657) ∧
    -Real.log (500000000000 / 612073672657) ≤ (101122279 / 500000000) := by
  have h := checkLog_sound (w := (112073672657 / 1112073672657)) (n := 12)
    (lo := (202244557 / 1000000000)) (hi := (101122279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612073672657 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612073672657 / 500000000000) = 1/(500000000000 / 612073672657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6953 : Bounds (202244557 / 1000000000) (101122279 / 500000000) (Real.log (612073672657 / 500000000000)) := by
  have h := reflection_log_6953_neg
  have he : Real.log (612073672657 / 500000000000) = -Real.log (500000000000 / 612073672657) := by
    rw [show ((612073672657 / 500000000000) : ℝ) = ((500000000000 / 612073672657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6954_neg : (202524229 / 500000000) ≤ -Real.log (100000000000 / 149937515621) ∧
    -Real.log (100000000000 / 149937515621) ≤ (405048459 / 1000000000) := by
  have h := checkLog_sound (w := (49937515621 / 249937515621)) (n := 12)
    (lo := (202524229 / 500000000)) (hi := (405048459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149937515621 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149937515621 / 100000000000) = 1/(100000000000 / 149937515621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6954 : Bounds (202524229 / 500000000) (405048459 / 1000000000) (Real.log (149937515621 / 100000000000)) := by
  have h := reflection_log_6954_neg
  have he : Real.log (149937515621 / 100000000000) = -Real.log (100000000000 / 149937515621) := by
    rw [show ((149937515621 / 100000000000) : ℝ) = ((100000000000 / 149937515621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6955_neg : (405256779 / 1000000000) ≤ -Real.log (500000000000 / 749843769529) ∧
    -Real.log (500000000000 / 749843769529) ≤ (20262839 / 50000000) := by
  have h := checkLog_sound (w := (249843769529 / 1249843769529)) (n := 12)
    (lo := (405256779 / 1000000000)) (hi := (20262839 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749843769529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749843769529 / 500000000000) = 1/(500000000000 / 749843769529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6955 : Bounds (405256779 / 1000000000) (20262839 / 50000000) (Real.log (749843769529 / 500000000000)) := by
  have h := reflection_log_6955_neg
  have he : Real.log (749843769529 / 500000000000) = -Real.log (500000000000 / 749843769529) := by
    rw [show ((749843769529 / 500000000000) : ℝ) = ((500000000000 / 749843769529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6956_neg : (45580389 / 250000000) ≤ -Real.log (5 / 6) ∧
    -Real.log (5 / 6) ≤ (182321557 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 11)) (n := 12)
    (lo := (45580389 / 250000000)) (hi := (182321557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6 / 5) = 1/(5 / 6) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6956 : Bounds (45580389 / 250000000) (182321557 / 1000000000) (Real.log (6 / 5)) := by
  have h := reflection_log_6956_neg
  have he : Real.log (6 / 5) = -Real.log (5 / 6) := by
    rw [show ((6 / 5) : ℝ) = ((5 / 6) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6957_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
    -Real.log (4 / 5) ≤ (1743309 / 7812500) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 4) = 1/(4 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6957 : Bounds (-1743309 / 7812500) (-223143551 / 1000000000) (Real.log (4 / 5)) := by
  have h := reflection_log_6957_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6958_neg : (9999 / 50000000) ≤ -Real.log (5000 / 5001) ∧
    -Real.log (5000 / 5001) ≤ (199981 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 10001)) (n := 12)
    (lo := (9999 / 50000000)) (hi := (199981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5001 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5001 / 5000) = 1/(5000 / 5001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6958 : Bounds (9999 / 50000000) (199981 / 1000000000) (Real.log (5001 / 5000)) := by
  have h := reflection_log_6958_neg
  have he : Real.log (5001 / 5000) = -Real.log (5000 / 5001) := by
    rw [show ((5001 / 5000) : ℝ) = ((5000 / 5001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6959_neg : (10001 / 50000000) ≤ -Real.log (4999 / 5000) ∧
    -Real.log (4999 / 5000) ≤ (200021 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 9999)) (n := 12)
    (lo := (10001 / 50000000)) (hi := (200021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4999) = 1/(4999 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6959 : Bounds (-200021 / 1000000000) (-10001 / 50000000) (Real.log (4999 / 5000)) := by
  have h := reflection_log_6959_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6960_neg : (23959101 / 250000000) ≤ -Real.log (1000000 / 1100579) ∧
    -Real.log (1000000 / 1100579) ≤ (19167281 / 200000000) := by
  have h := checkLog_sound (w := (100579 / 2100579)) (n := 12)
    (lo := (23959101 / 250000000)) (hi := (19167281 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100579 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100579 / 1000000) = 1/(1000000 / 1100579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6960 : Bounds (23959101 / 250000000) (19167281 / 200000000) (Real.log (1100579 / 1000000)) := by
  have h := reflection_log_6960_neg
  have he : Real.log (1100579 / 1000000) = -Real.log (1000000 / 1100579) := by
    rw [show ((1100579 / 1000000) : ℝ) = ((1000000 / 1100579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6961_neg : (13250507 / 125000000) ≤ -Real.log (899421 / 1000000) ∧
    -Real.log (899421 / 1000000) ≤ (106004057 / 1000000000) := by
  have h := checkLog_sound (w := (100579 / 1899421)) (n := 12)
    (lo := (13250507 / 125000000)) (hi := (106004057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899421) = 1/(899421 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6961 : Bounds (-106004057 / 1000000000) (-13250507 / 125000000) (Real.log (899421 / 1000000)) := by
  have h := reflection_log_6961_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6962_neg : (2401611 / 25000000) ≤ -Real.log (100000 / 110083) ∧
    -Real.log (100000 / 110083) ≤ (96064441 / 1000000000) := by
  have h := checkLog_sound (w := (10083 / 210083)) (n := 12)
    (lo := (2401611 / 25000000)) (hi := (96064441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110083 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(110083 / 100000) = 1/(100000 / 110083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6962 : Bounds (2401611 / 25000000) (96064441 / 1000000000) (Real.log (110083 / 100000)) := by
  have h := reflection_log_6962_neg
  have he : Real.log (110083 / 100000) = -Real.log (100000 / 110083) := by
    rw [show ((110083 / 100000) : ℝ) = ((100000 / 110083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6963_neg : (106283163 / 1000000000) ≤ -Real.log (89917 / 100000) ∧
    -Real.log (89917 / 100000) ≤ (26570791 / 250000000) := by
  have h := checkLog_sound (w := (10083 / 189917)) (n := 12)
    (lo := (106283163 / 1000000000)) (hi := (26570791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 89917) = 1/(89917 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6963 : Bounds (-26570791 / 250000000) (-106283163 / 1000000000) (Real.log (89917 / 100000)) := by
  have h := reflection_log_6963_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6964_neg : (5109361 / 500000000) ≤ -Real.log (9898333111 / 10000000000) ∧
    -Real.log (9898333111 / 10000000000) ≤ (10218723 / 1000000000) := by
  have h := checkLog_sound (w := (101666889 / 19898333111)) (n := 12)
    (lo := (5109361 / 500000000)) (hi := (10218723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9898333111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9898333111) = 1/(9898333111 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6964 : Bounds (-10218723 / 1000000000) (-5109361 / 500000000) (Real.log (9898333111 / 10000000000)) := by
  have h := reflection_log_6964_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6965_neg : (10167651 / 1000000000) ≤ -Real.log (989883864759 / 1000000000000) ∧
    -Real.log (989883864759 / 1000000000000) ≤ (2541913 / 250000000) := by
  have h := checkLog_sound (w := (10116135241 / 1989883864759)) (n := 12)
    (lo := (10167651 / 1000000000)) (hi := (2541913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989883864759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989883864759) = 1/(989883864759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6965 : Bounds (-2541913 / 250000000) (-10167651 / 1000000000) (Real.log (989883864759 / 1000000000000)) := by
  have h := reflection_log_6965_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6966_neg : (10092023 / 50000000) ≤ -Real.log (250000000000 / 305913193043) ∧
    -Real.log (250000000000 / 305913193043) ≤ (201840461 / 1000000000) := by
  have h := checkLog_sound (w := (55913193043 / 555913193043)) (n := 12)
    (lo := (10092023 / 50000000)) (hi := (201840461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305913193043 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305913193043 / 250000000000) = 1/(250000000000 / 305913193043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6966 : Bounds (10092023 / 50000000) (201840461 / 1000000000) (Real.log (305913193043 / 250000000000)) := by
  have h := reflection_log_6966_neg
  have he : Real.log (305913193043 / 250000000000) = -Real.log (250000000000 / 305913193043) := by
    rw [show ((305913193043 / 250000000000) : ℝ) = ((250000000000 / 305913193043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6967_neg : (50586901 / 250000000) ≤ -Real.log (100000000000 / 122427349667) ∧
    -Real.log (100000000000 / 122427349667) ≤ (40469521 / 200000000) := by
  have h := checkLog_sound (w := (22427349667 / 222427349667)) (n := 12)
    (lo := (50586901 / 250000000)) (hi := (40469521 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122427349667 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122427349667 / 100000000000) = 1/(100000000000 / 122427349667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6967 : Bounds (50586901 / 250000000) (40469521 / 200000000) (Real.log (122427349667 / 100000000000)) := by
  have h := reflection_log_6967_neg
  have he : Real.log (122427349667 / 100000000000) = -Real.log (100000000000 / 122427349667) := by
    rw [show ((122427349667 / 100000000000) : ℝ) = ((100000000000 / 122427349667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6968_neg : (405256779 / 1000000000) ≤ -Real.log (62500000000 / 93730471191) ∧
    -Real.log (62500000000 / 93730471191) ≤ (20262839 / 50000000) := by
  have h := checkLog_sound (w := (31230471191 / 156230471191)) (n := 12)
    (lo := (405256779 / 1000000000)) (hi := (20262839 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93730471191 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93730471191 / 62500000000) = 1/(62500000000 / 93730471191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6968 : Bounds (405256779 / 1000000000) (20262839 / 50000000) (Real.log (93730471191 / 62500000000)) := by
  have h := reflection_log_6968_neg
  have he : Real.log (93730471191 / 62500000000) = -Real.log (62500000000 / 93730471191) := by
    rw [show ((93730471191 / 62500000000) : ℝ) = ((62500000000 / 93730471191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6969_neg : (101366277 / 250000000) ≤ -Real.log (2 / 3) ∧
    -Real.log (2 / 3) ≤ (405465109 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3 / 2) = 1/(2 / 3) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6969 : Bounds (101366277 / 250000000) (405465109 / 1000000000) (Real.log (3 / 2)) := by
  have h := reflection_log_6969_neg
  have he : Real.log (3 / 2) = -Real.log (2 / 3) := by
    rw [show ((3 / 2) : ℝ) = ((2 / 3) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6970_neg : (22842267 / 125000000) ≤ -Real.log (2000 / 2401) ∧
    -Real.log (2000 / 2401) ≤ (182738137 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 4401)) (n := 12)
    (lo := (22842267 / 125000000)) (hi := (182738137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2401 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2401 / 2000) = 1/(2000 / 2401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6970 : Bounds (22842267 / 125000000) (182738137 / 1000000000) (Real.log (2401 / 2000)) := by
  have h := reflection_log_6970_neg
  have he : Real.log (2401 / 2000) = -Real.log (2000 / 2401) := by
    rw [show ((2401 / 2000) : ℝ) = ((2000 / 2401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6971_neg : (111884373 / 500000000) ≤ -Real.log (1599 / 2000) ∧
    -Real.log (1599 / 2000) ≤ (223768747 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 3599)) (n := 12)
    (lo := (111884373 / 500000000)) (hi := (223768747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1599) = 1/(1599 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6971 : Bounds (-223768747 / 1000000000) (-111884373 / 500000000) (Real.log (1599 / 2000)) := by
  have h := reflection_log_6971_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6972_neg : (200479 / 1000000000) ≤ -Real.log (2000000 / 2000401) ∧
    -Real.log (2000000 / 2000401) ≤ (1253 / 6250000) := by
  have h := checkLog_sound (w := (401 / 4000401)) (n := 12)
    (lo := (200479 / 1000000000)) (hi := (1253 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000401 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000401 / 2000000) = 1/(2000000 / 2000401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6972 : Bounds (200479 / 1000000000) (1253 / 6250000) (Real.log (2000401 / 2000000)) := by
  have h := reflection_log_6972_neg
  have he : Real.log (2000401 / 2000000) = -Real.log (2000000 / 2000401) := by
    rw [show ((2000401 / 2000000) : ℝ) = ((2000000 / 2000401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6973_neg : (5013 / 25000000) ≤ -Real.log (1999599 / 2000000) ∧
    -Real.log (1999599 / 2000000) ≤ (200521 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 3999599)) (n := 12)
    (lo := (5013 / 25000000)) (hi := (200521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999599) = 1/(1999599 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6973 : Bounds (-200521 / 1000000000) (-5013 / 25000000) (Real.log (1999599 / 2000000)) := by
  have h := reflection_log_6973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6974_neg : (95882743 / 1000000000) ≤ -Real.log (100000 / 110063) ∧
    -Real.log (100000 / 110063) ≤ (11985343 / 125000000) := by
  have h := checkLog_sound (w := (10063 / 210063)) (n := 12)
    (lo := (95882743 / 1000000000)) (hi := (11985343 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110063 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(110063 / 100000) = 1/(100000 / 110063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6974 : Bounds (95882743 / 1000000000) (11985343 / 125000000) (Real.log (110063 / 100000)) := by
  have h := reflection_log_6974_neg
  have he : Real.log (110063 / 100000) = -Real.log (100000 / 110063) := by
    rw [show ((110063 / 100000) : ℝ) = ((100000 / 110063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6975_neg : (2651519 / 25000000) ≤ -Real.log (89937 / 100000) ∧
    -Real.log (89937 / 100000) ≤ (106060761 / 1000000000) := by
  have h := checkLog_sound (w := (10063 / 189937)) (n := 12)
    (lo := (2651519 / 25000000)) (hi := (106060761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 89937) = 1/(89937 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6975 : Bounds (-106060761 / 1000000000) (-2651519 / 25000000) (Real.log (89937 / 100000)) := by
  have h := reflection_log_6975_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

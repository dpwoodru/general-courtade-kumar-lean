import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1856_neg : (13182 / 1953125) ≤ -Real.log (39730941591 / 40000000000) ∧
    -Real.log (39730941591 / 40000000000) ≤ (1349837 / 200000000) := by
  have h := checkLog_sound (w := (269058409 / 79730941591)) (n := 12)
    (lo := (13182 / 1953125)) (hi := (1349837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39730941591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39730941591) = 1/(39730941591 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1856 : Bounds (-1349837 / 200000000) (-13182 / 1953125) (Real.log (39730941591 / 40000000000)) := by
  have h := reflection_log_1856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1857_neg : (164399271 / 1000000000) ≤ -Real.log (500000000000 / 589342418449) ∧
    -Real.log (500000000000 / 589342418449) ≤ (20549909 / 125000000) := by
  have h := checkLog_sound (w := (89342418449 / 1089342418449)) (n := 12)
    (lo := (164399271 / 1000000000)) (hi := (20549909 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589342418449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589342418449 / 500000000000) = 1/(500000000000 / 589342418449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1857 : Bounds (164399271 / 1000000000) (20549909 / 125000000) (Real.log (589342418449 / 500000000000)) := by
  have h := reflection_log_1857_neg
  have he : Real.log (589342418449 / 500000000000) = -Real.log (500000000000 / 589342418449) := by
    rw [show ((589342418449 / 500000000000) : ℝ) = ((500000000000 / 589342418449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1858_neg : (164830177 / 1000000000) ≤ -Real.log (500000000000 / 589596424381) ∧
    -Real.log (500000000000 / 589596424381) ≤ (82415089 / 500000000) := by
  have h := checkLog_sound (w := (89596424381 / 1089596424381)) (n := 12)
    (lo := (164830177 / 1000000000)) (hi := (82415089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589596424381 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589596424381 / 500000000000) = 1/(500000000000 / 589596424381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1858 : Bounds (164830177 / 1000000000) (82415089 / 500000000) (Real.log (589596424381 / 500000000000)) := by
  have h := reflection_log_1858_neg
  have he : Real.log (589596424381 / 500000000000) = -Real.log (500000000000 / 589596424381) := by
    rw [show ((589596424381 / 500000000000) : ℝ) = ((500000000000 / 589596424381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1859_neg : (82438993 / 250000000) ≤ -Real.log (250000000000 / 347657183839) ∧
    -Real.log (250000000000 / 347657183839) ≤ (329755973 / 1000000000) := by
  have h := checkLog_sound (w := (97657183839 / 597657183839)) (n := 12)
    (lo := (82438993 / 250000000)) (hi := (329755973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347657183839 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347657183839 / 250000000000) = 1/(250000000000 / 347657183839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1859 : Bounds (82438993 / 250000000) (329755973 / 1000000000) (Real.log (347657183839 / 250000000000)) := by
  have h := reflection_log_1859_neg
  have he : Real.log (347657183839 / 250000000000) = -Real.log (250000000000 / 347657183839) := by
    rw [show ((347657183839 / 250000000000) : ℝ) = ((250000000000 / 347657183839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1860_neg : (164980731 / 500000000) ≤ -Real.log (500000000000 / 695457262403) ∧
    -Real.log (500000000000 / 695457262403) ≤ (329961463 / 1000000000) := by
  have h := checkLog_sound (w := (195457262403 / 1195457262403)) (n := 12)
    (lo := (164980731 / 500000000)) (hi := (329961463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695457262403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695457262403 / 500000000000) = 1/(500000000000 / 695457262403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1860 : Bounds (164980731 / 500000000) (329961463 / 1000000000) (Real.log (695457262403 / 500000000000)) := by
  have h := reflection_log_1860_neg
  have he : Real.log (695457262403 / 500000000000) = -Real.log (500000000000 / 695457262403) := by
    rw [show ((695457262403 / 500000000000) : ℝ) = ((500000000000 / 695457262403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1861_neg : (151518647 / 1000000000) ≤ -Real.log (2500 / 2909) ∧
    -Real.log (2500 / 2909) ≤ (18939831 / 125000000) := by
  have h := checkLog_sound (w := (409 / 5409)) (n := 12)
    (lo := (151518647 / 1000000000)) (hi := (18939831 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2909 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2909 / 2500) = 1/(2500 / 2909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1861 : Bounds (151518647 / 1000000000) (18939831 / 125000000) (Real.log (2909 / 2500)) := by
  have h := reflection_log_1861_neg
  have he : Real.log (2909 / 2500) = -Real.log (2500 / 2909) := by
    rw [show ((2909 / 2500) : ℝ) = ((2500 / 2909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1862_neg : (178648311 / 1000000000) ≤ -Real.log (2091 / 2500) ∧
    -Real.log (2091 / 2500) ≤ (22331039 / 125000000) := by
  have h := checkLog_sound (w := (409 / 4591)) (n := 12)
    (lo := (178648311 / 1000000000)) (hi := (22331039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2091) = 1/(2091 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1862 : Bounds (-22331039 / 125000000) (-178648311 / 1000000000) (Real.log (2091 / 2500)) := by
  have h := reflection_log_1862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1863_neg : (81793 / 500000000) ≤ -Real.log (2500000 / 2500409) ∧
    -Real.log (2500000 / 2500409) ≤ (163587 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 5000409)) (n := 12)
    (lo := (81793 / 500000000)) (hi := (163587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500409 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500409 / 2500000) = 1/(2500000 / 2500409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1863 : Bounds (81793 / 500000000) (163587 / 1000000000) (Real.log (2500409 / 2500000)) := by
  have h := reflection_log_1863_neg
  have he : Real.log (2500409 / 2500000) = -Real.log (2500000 / 2500409) := by
    rw [show ((2500409 / 2500000) : ℝ) = ((2500000 / 2500409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1864_neg : (163613 / 1000000000) ≤ -Real.log (2499591 / 2500000) ∧
    -Real.log (2499591 / 2500000) ≤ (81807 / 500000000) := by
  have h := checkLog_sound (w := (409 / 4999591)) (n := 12)
    (lo := (163613 / 1000000000)) (hi := (81807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499591) = 1/(2499591 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1864 : Bounds (-81807 / 500000000) (-163613 / 1000000000) (Real.log (2499591 / 2500000)) := by
  have h := reflection_log_1864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1865_neg : (19717813 / 250000000) ≤ -Real.log (200000 / 216413) ∧
    -Real.log (200000 / 216413) ≤ (78871253 / 1000000000) := by
  have h := checkLog_sound (w := (16413 / 416413)) (n := 12)
    (lo := (19717813 / 250000000)) (hi := (78871253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216413 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216413 / 200000) = 1/(200000 / 216413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1865 : Bounds (19717813 / 250000000) (78871253 / 1000000000) (Real.log (216413 / 200000)) := by
  have h := reflection_log_1865_neg
  have he : Real.log (216413 / 200000) = -Real.log (200000 / 216413) := by
    rw [show ((216413 / 200000) : ℝ) = ((200000 / 216413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1866_neg : (10703587 / 125000000) ≤ -Real.log (183587 / 200000) ∧
    -Real.log (183587 / 200000) ≤ (85628697 / 1000000000) := by
  have h := checkLog_sound (w := (16413 / 383587)) (n := 12)
    (lo := (10703587 / 125000000)) (hi := (85628697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183587) = 1/(183587 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1866 : Bounds (-85628697 / 1000000000) (-10703587 / 125000000) (Real.log (183587 / 200000)) := by
  have h := reflection_log_1866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1867_neg : (39534963 / 500000000) ≤ -Real.log (25000 / 27057) ∧
    -Real.log (25000 / 27057) ≤ (79069927 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 52057)) (n := 12)
    (lo := (39534963 / 500000000)) (hi := (79069927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27057 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27057 / 25000) = 1/(25000 / 27057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1867 : Bounds (39534963 / 500000000) (79069927 / 1000000000) (Real.log (27057 / 25000)) := by
  have h := reflection_log_1867_neg
  have he : Real.log (27057 / 25000) = -Real.log (25000 / 27057) := by
    rw [show ((27057 / 25000) : ℝ) = ((25000 / 27057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1868_neg : (17172589 / 200000000) ≤ -Real.log (22943 / 25000) ∧
    -Real.log (22943 / 25000) ≤ (42931473 / 500000000) := by
  have h := checkLog_sound (w := (2057 / 47943)) (n := 12)
    (lo := (17172589 / 200000000)) (hi := (42931473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22943) = 1/(22943 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1868 : Bounds (-42931473 / 500000000) (-17172589 / 200000000) (Real.log (22943 / 25000)) := by
  have h := reflection_log_1868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1869_neg : (3396509 / 500000000) ≤ -Real.log (620768751 / 625000000) ∧
    -Real.log (620768751 / 625000000) ≤ (6793019 / 1000000000) := by
  have h := checkLog_sound (w := (4231249 / 1245768751)) (n := 12)
    (lo := (3396509 / 500000000)) (hi := (6793019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 620768751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 620768751) = 1/(620768751 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1869 : Bounds (-6793019 / 1000000000) (-3396509 / 500000000) (Real.log (620768751 / 625000000)) := by
  have h := reflection_log_1869_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1870_neg : (1689361 / 250000000) ≤ -Real.log (39730613431 / 40000000000) ∧
    -Real.log (39730613431 / 40000000000) ≤ (1351489 / 200000000) := by
  have h := checkLog_sound (w := (269386569 / 79730613431)) (n := 12)
    (lo := (1689361 / 250000000)) (hi := (1351489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39730613431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39730613431) = 1/(39730613431 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1870 : Bounds (-1351489 / 200000000) (-1689361 / 250000000) (Real.log (39730613431 / 40000000000)) := by
  have h := reflection_log_1870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1871_neg : (164499949 / 1000000000) ≤ -Real.log (250000000000 / 294700877513) ∧
    -Real.log (250000000000 / 294700877513) ≤ (3289999 / 20000000) := by
  have h := checkLog_sound (w := (44700877513 / 544700877513)) (n := 12)
    (lo := (164499949 / 1000000000)) (hi := (3289999 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294700877513 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294700877513 / 250000000000) = 1/(250000000000 / 294700877513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1871 : Bounds (164499949 / 1000000000) (3289999 / 20000000) (Real.log (294700877513 / 250000000000)) := by
  have h := reflection_log_1871_neg
  have he : Real.log (294700877513 / 250000000000) = -Real.log (250000000000 / 294700877513) := by
    rw [show ((294700877513 / 250000000000) : ℝ) = ((250000000000 / 294700877513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1872_neg : (20616609 / 125000000) ≤ -Real.log (31250000000 / 36853560999) ∧
    -Real.log (31250000000 / 36853560999) ≤ (164932873 / 1000000000) := by
  have h := checkLog_sound (w := (5603560999 / 68103560999)) (n := 12)
    (lo := (20616609 / 125000000)) (hi := (164932873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36853560999 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36853560999 / 31250000000) = 1/(31250000000 / 36853560999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1872 : Bounds (20616609 / 125000000) (164932873 / 1000000000) (Real.log (36853560999 / 31250000000)) := by
  have h := reflection_log_1872_neg
  have he : Real.log (36853560999 / 31250000000) = -Real.log (31250000000 / 36853560999) := by
    rw [show ((36853560999 / 31250000000) : ℝ) = ((31250000000 / 36853560999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1873_neg : (164980731 / 500000000) ≤ -Real.log (250000000000 / 347728631201) ∧
    -Real.log (250000000000 / 347728631201) ≤ (329961463 / 1000000000) := by
  have h := checkLog_sound (w := (97728631201 / 597728631201)) (n := 12)
    (lo := (164980731 / 500000000)) (hi := (329961463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347728631201 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347728631201 / 250000000000) = 1/(250000000000 / 347728631201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1873 : Bounds (164980731 / 500000000) (329961463 / 1000000000) (Real.log (347728631201 / 250000000000)) := by
  have h := reflection_log_1873_neg
  have he : Real.log (347728631201 / 250000000000) = -Real.log (250000000000 / 347728631201) := by
    rw [show ((347728631201 / 250000000000) : ℝ) = ((250000000000 / 347728631201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1874_neg : (330166959 / 1000000000) ≤ -Real.log (500000000000 / 695600191297) ∧
    -Real.log (500000000000 / 695600191297) ≤ (4127087 / 12500000) := by
  have h := checkLog_sound (w := (195600191297 / 1195600191297)) (n := 12)
    (lo := (330166959 / 1000000000)) (hi := (4127087 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695600191297 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695600191297 / 500000000000) = 1/(500000000000 / 695600191297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1874 : Bounds (330166959 / 1000000000) (4127087 / 12500000) (Real.log (695600191297 / 500000000000)) := by
  have h := reflection_log_1874_neg
  have he : Real.log (695600191297 / 500000000000) = -Real.log (500000000000 / 695600191297) := by
    rw [show ((695600191297 / 500000000000) : ℝ) = ((500000000000 / 695600191297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1875_neg : (18950573 / 125000000) ≤ -Real.log (10000 / 11637) ∧
    -Real.log (10000 / 11637) ≤ (30320917 / 200000000) := by
  have h := checkLog_sound (w := (1637 / 21637)) (n := 12)
    (lo := (18950573 / 125000000)) (hi := (30320917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11637 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11637 / 10000) = 1/(10000 / 11637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1875 : Bounds (18950573 / 125000000) (30320917 / 200000000) (Real.log (11637 / 10000)) := by
  have h := reflection_log_1875_neg
  have he : Real.log (11637 / 10000) = -Real.log (10000 / 11637) := by
    rw [show ((11637 / 10000) : ℝ) = ((10000 / 11637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1876_neg : (89383939 / 500000000) ≤ -Real.log (8363 / 10000) ∧
    -Real.log (8363 / 10000) ≤ (178767879 / 1000000000) := by
  have h := checkLog_sound (w := (1637 / 18363)) (n := 12)
    (lo := (89383939 / 500000000)) (hi := (178767879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8363) = 1/(8363 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1876 : Bounds (-178767879 / 1000000000) (-89383939 / 500000000) (Real.log (8363 / 10000)) := by
  have h := reflection_log_1876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1877_neg : (81843 / 500000000) ≤ -Real.log (10000000 / 10001637) ∧
    -Real.log (10000000 / 10001637) ≤ (163687 / 1000000000) := by
  have h := checkLog_sound (w := (1637 / 20001637)) (n := 12)
    (lo := (81843 / 500000000)) (hi := (163687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001637 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001637 / 10000000) = 1/(10000000 / 10001637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1877 : Bounds (81843 / 500000000) (163687 / 1000000000) (Real.log (10001637 / 10000000)) := by
  have h := reflection_log_1877_neg
  have he : Real.log (10001637 / 10000000) = -Real.log (10000000 / 10001637) := by
    rw [show ((10001637 / 10000000) : ℝ) = ((10000000 / 10001637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1878_neg : (163713 / 1000000000) ≤ -Real.log (9998363 / 10000000) ∧
    -Real.log (9998363 / 10000000) ≤ (81857 / 500000000) := by
  have h := checkLog_sound (w := (1637 / 19998363)) (n := 12)
    (lo := (163713 / 1000000000)) (hi := (81857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998363) = 1/(9998363 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1878 : Bounds (-81857 / 500000000) (-163713 / 1000000000) (Real.log (9998363 / 10000000)) := by
  have h := reflection_log_1878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1879_neg : (78918383 / 1000000000) ≤ -Real.log (250000 / 270529) ∧
    -Real.log (250000 / 270529) ≤ (4932399 / 62500000) := by
  have h := checkLog_sound (w := (20529 / 520529)) (n := 12)
    (lo := (78918383 / 1000000000)) (hi := (4932399 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270529 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270529 / 250000) = 1/(250000 / 270529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1879 : Bounds (78918383 / 1000000000) (4932399 / 62500000) (Real.log (270529 / 250000)) := by
  have h := reflection_log_1879_neg
  have he : Real.log (270529 / 250000) = -Real.log (250000 / 270529) := by
    rw [show ((270529 / 250000) : ℝ) = ((250000 / 270529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1880_neg : (42842129 / 500000000) ≤ -Real.log (229471 / 250000) ∧
    -Real.log (229471 / 250000) ≤ (85684259 / 1000000000) := by
  have h := checkLog_sound (w := (20529 / 479471)) (n := 12)
    (lo := (42842129 / 500000000)) (hi := (85684259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229471) = 1/(229471 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1880 : Bounds (-85684259 / 1000000000) (-42842129 / 500000000) (Real.log (229471 / 250000)) := by
  have h := reflection_log_1880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1881_neg : (9889631 / 125000000) ≤ -Real.log (1000000 / 1082331) ∧
    -Real.log (1000000 / 1082331) ≤ (79117049 / 1000000000) := by
  have h := checkLog_sound (w := (82331 / 2082331)) (n := 12)
    (lo := (9889631 / 125000000)) (hi := (79117049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082331 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082331 / 1000000) = 1/(1000000 / 1082331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1881 : Bounds (9889631 / 125000000) (79117049 / 1000000000) (Real.log (1082331 / 1000000)) := by
  have h := reflection_log_1881_neg
  have he : Real.log (1082331 / 1000000) = -Real.log (1000000 / 1082331) := by
    rw [show ((1082331 / 1000000) : ℝ) = ((1000000 / 1082331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1882_neg : (85918519 / 1000000000) ≤ -Real.log (917669 / 1000000) ∧
    -Real.log (917669 / 1000000) ≤ (2147963 / 25000000) := by
  have h := checkLog_sound (w := (82331 / 1917669)) (n := 12)
    (lo := (85918519 / 1000000000)) (hi := (2147963 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917669) = 1/(917669 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1882 : Bounds (-2147963 / 25000000) (-85918519 / 1000000000) (Real.log (917669 / 1000000)) := by
  have h := reflection_log_1882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1883_neg : (6801471 / 1000000000) ≤ -Real.log (993221606439 / 1000000000000) ∧
    -Real.log (993221606439 / 1000000000000) ≤ (106273 / 15625000) := by
  have h := checkLog_sound (w := (6778393561 / 1993221606439)) (n := 12)
    (lo := (6801471 / 1000000000)) (hi := (106273 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993221606439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993221606439) = 1/(993221606439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1883 : Bounds (-106273 / 15625000) (-6801471 / 1000000000) (Real.log (993221606439 / 1000000000000)) := by
  have h := reflection_log_1883_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1884_neg : (3382937 / 500000000) ≤ -Real.log (62078560159 / 62500000000) ∧
    -Real.log (62078560159 / 62500000000) ≤ (54127 / 8000000) := by
  have h := checkLog_sound (w := (421439841 / 124578560159)) (n := 12)
    (lo := (3382937 / 500000000)) (hi := (54127 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62078560159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62078560159) = 1/(62078560159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1884 : Bounds (-54127 / 8000000) (-3382937 / 500000000) (Real.log (62078560159 / 62500000000)) := by
  have h := reflection_log_1884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1885_neg : (164602641 / 1000000000) ≤ -Real.log (250000000000 / 294731142497) ∧
    -Real.log (250000000000 / 294731142497) ≤ (82301321 / 500000000) := by
  have h := checkLog_sound (w := (44731142497 / 544731142497)) (n := 12)
    (lo := (164602641 / 1000000000)) (hi := (82301321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294731142497 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294731142497 / 250000000000) = 1/(250000000000 / 294731142497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1885 : Bounds (164602641 / 1000000000) (82301321 / 500000000) (Real.log (294731142497 / 250000000000)) := by
  have h := reflection_log_1885_neg
  have he : Real.log (294731142497 / 250000000000) = -Real.log (250000000000 / 294731142497) := by
    rw [show ((294731142497 / 250000000000) : ℝ) = ((250000000000 / 294731142497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1886_neg : (10314723 / 62500000) ≤ -Real.log (250000000000 / 294858767159) ∧
    -Real.log (250000000000 / 294858767159) ≤ (165035569 / 1000000000) := by
  have h := checkLog_sound (w := (44858767159 / 544858767159)) (n := 12)
    (lo := (10314723 / 62500000)) (hi := (165035569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294858767159 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294858767159 / 250000000000) = 1/(250000000000 / 294858767159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1886 : Bounds (10314723 / 62500000) (165035569 / 1000000000) (Real.log (294858767159 / 250000000000)) := by
  have h := reflection_log_1886_neg
  have he : Real.log (294858767159 / 250000000000) = -Real.log (250000000000 / 294858767159) := by
    rw [show ((294858767159 / 250000000000) : ℝ) = ((250000000000 / 294858767159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1887_neg : (330166959 / 1000000000) ≤ -Real.log (7812500000 / 10868752989) ∧
    -Real.log (7812500000 / 10868752989) ≤ (4127087 / 12500000) := by
  have h := checkLog_sound (w := (3056252989 / 18681252989)) (n := 12)
    (lo := (330166959 / 1000000000)) (hi := (4127087 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10868752989 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10868752989 / 7812500000) = 1/(7812500000 / 10868752989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1887 : Bounds (330166959 / 1000000000) (4127087 / 12500000) (Real.log (10868752989 / 7812500000)) := by
  have h := reflection_log_1887_neg
  have he : Real.log (10868752989 / 7812500000) = -Real.log (7812500000 / 10868752989) := by
    rw [show ((10868752989 / 7812500000) : ℝ) = ((7812500000 / 10868752989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1888_neg : (165186231 / 500000000) ≤ -Real.log (500000000000 / 695743154371) ∧
    -Real.log (500000000000 / 695743154371) ≤ (330372463 / 1000000000) := by
  have h := checkLog_sound (w := (195743154371 / 1195743154371)) (n := 12)
    (lo := (165186231 / 500000000)) (hi := (330372463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695743154371 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695743154371 / 500000000000) = 1/(500000000000 / 695743154371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1888 : Bounds (165186231 / 500000000) (330372463 / 1000000000) (Real.log (695743154371 / 500000000000)) := by
  have h := reflection_log_1888_neg
  have he : Real.log (695743154371 / 500000000000) = -Real.log (500000000000 / 695743154371) := by
    rw [show ((695743154371 / 500000000000) : ℝ) = ((500000000000 / 695743154371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1889_neg : (151690513 / 1000000000) ≤ -Real.log (5000 / 5819) ∧
    -Real.log (5000 / 5819) ≤ (75845257 / 500000000) := by
  have h := checkLog_sound (w := (819 / 10819)) (n := 12)
    (lo := (151690513 / 1000000000)) (hi := (75845257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5819 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5819 / 5000) = 1/(5000 / 5819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1889 : Bounds (151690513 / 1000000000) (75845257 / 500000000) (Real.log (5819 / 5000)) := by
  have h := reflection_log_1889_neg
  have he : Real.log (5819 / 5000) = -Real.log (5000 / 5819) := by
    rw [show ((5819 / 5000) : ℝ) = ((5000 / 5819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1890_neg : (8944373 / 50000000) ≤ -Real.log (4181 / 5000) ∧
    -Real.log (4181 / 5000) ≤ (178887461 / 1000000000) := by
  have h := checkLog_sound (w := (819 / 9181)) (n := 12)
    (lo := (8944373 / 50000000)) (hi := (178887461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4181) = 1/(4181 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1890 : Bounds (-178887461 / 1000000000) (-8944373 / 50000000) (Real.log (4181 / 5000)) := by
  have h := reflection_log_1890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1891_neg : (81893 / 500000000) ≤ -Real.log (5000000 / 5000819) ∧
    -Real.log (5000000 / 5000819) ≤ (163787 / 1000000000) := by
  have h := checkLog_sound (w := (819 / 10000819)) (n := 12)
    (lo := (81893 / 500000000)) (hi := (163787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000819 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000819 / 5000000) = 1/(5000000 / 5000819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1891 : Bounds (81893 / 500000000) (163787 / 1000000000) (Real.log (5000819 / 5000000)) := by
  have h := reflection_log_1891_neg
  have he : Real.log (5000819 / 5000000) = -Real.log (5000000 / 5000819) := by
    rw [show ((5000819 / 5000000) : ℝ) = ((5000000 / 5000819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1892_neg : (163813 / 1000000000) ≤ -Real.log (4999181 / 5000000) ∧
    -Real.log (4999181 / 5000000) ≤ (81907 / 500000000) := by
  have h := checkLog_sound (w := (819 / 9999181)) (n := 12)
    (lo := (163813 / 1000000000)) (hi := (81907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999181) = 1/(4999181 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1892 : Bounds (-81907 / 500000000) (-163813 / 1000000000) (Real.log (4999181 / 5000000)) := by
  have h := reflection_log_1892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1893_neg : (9870689 / 125000000) ≤ -Real.log (1000000 / 1082167) ∧
    -Real.log (1000000 / 1082167) ≤ (78965513 / 1000000000) := by
  have h := checkLog_sound (w := (82167 / 2082167)) (n := 12)
    (lo := (9870689 / 125000000)) (hi := (78965513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082167 / 1000000) = 1/(1000000 / 1082167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1893 : Bounds (9870689 / 125000000) (78965513 / 1000000000) (Real.log (1082167 / 1000000)) := by
  have h := reflection_log_1893_neg
  have he : Real.log (1082167 / 1000000) = -Real.log (1000000 / 1082167) := by
    rw [show ((1082167 / 1000000) : ℝ) = ((1000000 / 1082167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1894_neg : (42869911 / 500000000) ≤ -Real.log (917833 / 1000000) ∧
    -Real.log (917833 / 1000000) ≤ (85739823 / 1000000000) := by
  have h := checkLog_sound (w := (82167 / 1917833)) (n := 12)
    (lo := (42869911 / 500000000)) (hi := (85739823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917833) = 1/(917833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1894 : Bounds (-85739823 / 1000000000) (-42869911 / 500000000) (Real.log (917833 / 1000000)) := by
  have h := reflection_log_1894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1895_neg : (19790811 / 250000000) ≤ -Real.log (1000000 / 1082381) ∧
    -Real.log (1000000 / 1082381) ≤ (15832649 / 200000000) := by
  have h := checkLog_sound (w := (82381 / 2082381)) (n := 12)
    (lo := (19790811 / 250000000)) (hi := (15832649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082381 / 1000000) = 1/(1000000 / 1082381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1895 : Bounds (19790811 / 250000000) (15832649 / 200000000) (Real.log (1082381 / 1000000)) := by
  have h := reflection_log_1895_neg
  have he : Real.log (1082381 / 1000000) = -Real.log (1000000 / 1082381) := by
    rw [show ((1082381 / 1000000) : ℝ) = ((1000000 / 1082381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1896_neg : (85973007 / 1000000000) ≤ -Real.log (917619 / 1000000) ∧
    -Real.log (917619 / 1000000) ≤ (5373313 / 62500000) := by
  have h := checkLog_sound (w := (82381 / 1917619)) (n := 12)
    (lo := (85973007 / 1000000000)) (hi := (5373313 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917619) = 1/(917619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1896 : Bounds (-5373313 / 62500000) (-85973007 / 1000000000) (Real.log (917619 / 1000000)) := by
  have h := reflection_log_1896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1897_neg : (6809763 / 1000000000) ≤ -Real.log (993213370839 / 1000000000000) ∧
    -Real.log (993213370839 / 1000000000000) ≤ (1702441 / 250000000) := by
  have h := checkLog_sound (w := (6786629161 / 1993213370839)) (n := 12)
    (lo := (6809763 / 1000000000)) (hi := (1702441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993213370839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993213370839) = 1/(993213370839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1897 : Bounds (-1702441 / 250000000) (-6809763 / 1000000000) (Real.log (993213370839 / 1000000000000)) := by
  have h := reflection_log_1897_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1898_neg : (6774309 / 1000000000) ≤ -Real.log (993248584111 / 1000000000000) ∧
    -Real.log (993248584111 / 1000000000000) ≤ (677431 / 100000000) := by
  have h := checkLog_sound (w := (6751415889 / 1993248584111)) (n := 12)
    (lo := (6774309 / 1000000000)) (hi := (677431 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993248584111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993248584111) = 1/(993248584111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1898 : Bounds (-677431 / 100000000) (-6774309 / 1000000000) (Real.log (993248584111 / 1000000000000)) := by
  have h := reflection_log_1898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1899_neg : (82352667 / 500000000) ≤ -Real.log (500000000000 / 589522821689) ∧
    -Real.log (500000000000 / 589522821689) ≤ (32941067 / 200000000) := by
  have h := checkLog_sound (w := (89522821689 / 1089522821689)) (n := 12)
    (lo := (82352667 / 500000000)) (hi := (32941067 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589522821689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589522821689 / 500000000000) = 1/(500000000000 / 589522821689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1899 : Bounds (82352667 / 500000000) (32941067 / 200000000) (Real.log (589522821689 / 500000000000)) := by
  have h := reflection_log_1899_neg
  have he : Real.log (589522821689 / 500000000000) = -Real.log (500000000000 / 589522821689) := by
    rw [show ((589522821689 / 500000000000) : ℝ) = ((500000000000 / 589522821689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1900_neg : (165136251 / 1000000000) ≤ -Real.log (500000000000 / 589776911769) ∧
    -Real.log (500000000000 / 589776911769) ≤ (41284063 / 250000000) := by
  have h := checkLog_sound (w := (89776911769 / 1089776911769)) (n := 12)
    (lo := (165136251 / 1000000000)) (hi := (41284063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589776911769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589776911769 / 500000000000) = 1/(500000000000 / 589776911769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1900 : Bounds (165136251 / 1000000000) (41284063 / 250000000) (Real.log (589776911769 / 500000000000)) := by
  have h := reflection_log_1900_neg
  have he : Real.log (589776911769 / 500000000000) = -Real.log (500000000000 / 589776911769) := by
    rw [show ((589776911769 / 500000000000) : ℝ) = ((500000000000 / 589776911769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1901_neg : (165186231 / 500000000) ≤ -Real.log (50000000000 / 69574315437) ∧
    -Real.log (50000000000 / 69574315437) ≤ (330372463 / 1000000000) := by
  have h := checkLog_sound (w := (19574315437 / 119574315437)) (n := 12)
    (lo := (165186231 / 500000000)) (hi := (330372463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69574315437 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69574315437 / 50000000000) = 1/(50000000000 / 69574315437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1901 : Bounds (165186231 / 500000000) (330372463 / 1000000000) (Real.log (69574315437 / 50000000000)) := by
  have h := reflection_log_1901_neg
  have he : Real.log (69574315437 / 50000000000) = -Real.log (50000000000 / 69574315437) := by
    rw [show ((69574315437 / 50000000000) : ℝ) = ((50000000000 / 69574315437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1902_neg : (330577973 / 1000000000) ≤ -Real.log (500000000000 / 695886151639) ∧
    -Real.log (500000000000 / 695886151639) ≤ (165288987 / 500000000) := by
  have h := checkLog_sound (w := (195886151639 / 1195886151639)) (n := 12)
    (lo := (330577973 / 1000000000)) (hi := (165288987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695886151639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695886151639 / 500000000000) = 1/(500000000000 / 695886151639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1902 : Bounds (330577973 / 1000000000) (165288987 / 500000000) (Real.log (695886151639 / 500000000000)) := by
  have h := reflection_log_1902_neg
  have he : Real.log (695886151639 / 500000000000) = -Real.log (500000000000 / 695886151639) := by
    rw [show ((695886151639 / 500000000000) : ℝ) = ((500000000000 / 695886151639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1903_neg : (75888217 / 500000000) ≤ -Real.log (10000 / 11639) ∧
    -Real.log (10000 / 11639) ≤ (30355287 / 200000000) := by
  have h := checkLog_sound (w := (1639 / 21639)) (n := 12)
    (lo := (75888217 / 500000000)) (hi := (30355287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11639 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11639 / 10000) = 1/(10000 / 11639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1903 : Bounds (75888217 / 500000000) (30355287 / 200000000) (Real.log (11639 / 10000)) := by
  have h := reflection_log_1903_neg
  have he : Real.log (11639 / 10000) = -Real.log (10000 / 11639) := by
    rw [show ((11639 / 10000) : ℝ) = ((10000 / 11639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1904_neg : (35801411 / 200000000) ≤ -Real.log (8361 / 10000) ∧
    -Real.log (8361 / 10000) ≤ (11187941 / 62500000) := by
  have h := checkLog_sound (w := (1639 / 18361)) (n := 12)
    (lo := (35801411 / 200000000)) (hi := (11187941 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8361) = 1/(8361 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1904 : Bounds (-11187941 / 62500000) (-35801411 / 200000000) (Real.log (8361 / 10000)) := by
  have h := reflection_log_1904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1905_neg : (81943 / 500000000) ≤ -Real.log (10000000 / 10001639) ∧
    -Real.log (10000000 / 10001639) ≤ (163887 / 1000000000) := by
  have h := checkLog_sound (w := (1639 / 20001639)) (n := 12)
    (lo := (81943 / 500000000)) (hi := (163887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001639 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001639 / 10000000) = 1/(10000000 / 10001639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1905 : Bounds (81943 / 500000000) (163887 / 1000000000) (Real.log (10001639 / 10000000)) := by
  have h := reflection_log_1905_neg
  have he : Real.log (10001639 / 10000000) = -Real.log (10000000 / 10001639) := by
    rw [show ((10001639 / 10000000) : ℝ) = ((10000000 / 10001639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1906_neg : (163913 / 1000000000) ≤ -Real.log (9998361 / 10000000) ∧
    -Real.log (9998361 / 10000000) ≤ (81957 / 500000000) := by
  have h := checkLog_sound (w := (1639 / 19998361)) (n := 12)
    (lo := (163913 / 1000000000)) (hi := (81957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998361) = 1/(9998361 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1906 : Bounds (-81957 / 500000000) (-163913 / 1000000000) (Real.log (9998361 / 10000000)) := by
  have h := reflection_log_1906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1907_neg : (39505857 / 500000000) ≤ -Real.log (1000000 / 1082217) ∧
    -Real.log (1000000 / 1082217) ≤ (15802343 / 200000000) := by
  have h := checkLog_sound (w := (82217 / 2082217)) (n := 12)
    (lo := (39505857 / 500000000)) (hi := (15802343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082217 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082217 / 1000000) = 1/(1000000 / 1082217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1907 : Bounds (39505857 / 500000000) (15802343 / 200000000) (Real.log (1082217 / 1000000)) := by
  have h := reflection_log_1907_neg
  have he : Real.log (1082217 / 1000000) = -Real.log (1000000 / 1082217) := by
    rw [show ((1082217 / 1000000) : ℝ) = ((1000000 / 1082217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1908_neg : (85794299 / 1000000000) ≤ -Real.log (917783 / 1000000) ∧
    -Real.log (917783 / 1000000) ≤ (857943 / 10000000) := by
  have h := checkLog_sound (w := (82217 / 1917783)) (n := 12)
    (lo := (85794299 / 1000000000)) (hi := (857943 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917783) = 1/(917783 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1908 : Bounds (-857943 / 10000000) (-85794299 / 1000000000) (Real.log (917783 / 1000000)) := by
  have h := reflection_log_1908_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1909_neg : (79210361 / 1000000000) ≤ -Real.log (15625 / 16913) ∧
    -Real.log (15625 / 16913) ≤ (39605181 / 500000000) := by
  have h := checkLog_sound (w := (644 / 16269)) (n := 12)
    (lo := (79210361 / 1000000000)) (hi := (39605181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16913 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16913 / 15625) = 1/(15625 / 16913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1909 : Bounds (79210361 / 1000000000) (39605181 / 500000000) (Real.log (16913 / 15625)) := by
  have h := reflection_log_1909_neg
  have he : Real.log (16913 / 15625) = -Real.log (15625 / 16913) := by
    rw [show ((16913 / 15625) : ℝ) = ((15625 / 16913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1910_neg : (86028587 / 1000000000) ≤ -Real.log (14337 / 15625) ∧
    -Real.log (14337 / 15625) ≤ (21507147 / 250000000) := by
  have h := checkLog_sound (w := (644 / 14981)) (n := 12)
    (lo := (86028587 / 1000000000)) (hi := (21507147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14337) = 1/(14337 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1910 : Bounds (-21507147 / 250000000) (-86028587 / 1000000000) (Real.log (14337 / 15625)) := by
  have h := reflection_log_1910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1911_neg : (272729 / 40000000) ≤ -Real.log (242481681 / 244140625) ∧
    -Real.log (242481681 / 244140625) ≤ (3409113 / 500000000) := by
  have h := checkLog_sound (w := (829472 / 243311153)) (n := 12)
    (lo := (272729 / 40000000)) (hi := (3409113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242481681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242481681) = 1/(242481681 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1911 : Bounds (-3409113 / 500000000) (-272729 / 40000000) (Real.log (242481681 / 244140625)) := by
  have h := reflection_log_1911_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1912_neg : (847823 / 125000000) ≤ -Real.log (993240364911 / 1000000000000) ∧
    -Real.log (993240364911 / 1000000000000) ≤ (1356517 / 200000000) := by
  have h := checkLog_sound (w := (6759635089 / 1993240364911)) (n := 12)
    (lo := (847823 / 125000000)) (hi := (1356517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993240364911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993240364911) = 1/(993240364911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1912 : Bounds (-1356517 / 200000000) (-847823 / 125000000) (Real.log (993240364911 / 1000000000000)) := by
  have h := reflection_log_1912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1913_neg : (82403007 / 500000000) ≤ -Real.log (250000000000 / 294791088961) ∧
    -Real.log (250000000000 / 294791088961) ≤ (32961203 / 200000000) := by
  have h := checkLog_sound (w := (44791088961 / 544791088961)) (n := 12)
    (lo := (82403007 / 500000000)) (hi := (32961203 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294791088961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294791088961 / 250000000000) = 1/(250000000000 / 294791088961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1913 : Bounds (82403007 / 500000000) (32961203 / 200000000) (Real.log (294791088961 / 250000000000)) := by
  have h := reflection_log_1913_neg
  have he : Real.log (294791088961 / 250000000000) = -Real.log (250000000000 / 294791088961) := by
    rw [show ((294791088961 / 250000000000) : ℝ) = ((250000000000 / 294791088961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1914_neg : (41309737 / 250000000) ≤ -Real.log (100000000000 / 117967496687) ∧
    -Real.log (100000000000 / 117967496687) ≤ (165238949 / 1000000000) := by
  have h := checkLog_sound (w := (17967496687 / 217967496687)) (n := 12)
    (lo := (41309737 / 250000000)) (hi := (165238949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117967496687 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117967496687 / 100000000000) = 1/(100000000000 / 117967496687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1914 : Bounds (41309737 / 250000000) (165238949 / 1000000000) (Real.log (117967496687 / 100000000000)) := by
  have h := reflection_log_1914_neg
  have he : Real.log (117967496687 / 100000000000) = -Real.log (100000000000 / 117967496687) := by
    rw [show ((117967496687 / 100000000000) : ℝ) = ((100000000000 / 117967496687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1915_neg : (330577973 / 1000000000) ≤ -Real.log (250000000000 / 347943075819) ∧
    -Real.log (250000000000 / 347943075819) ≤ (165288987 / 500000000) := by
  have h := checkLog_sound (w := (97943075819 / 597943075819)) (n := 12)
    (lo := (330577973 / 1000000000)) (hi := (165288987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347943075819 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347943075819 / 250000000000) = 1/(250000000000 / 347943075819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1915 : Bounds (330577973 / 1000000000) (165288987 / 500000000) (Real.log (347943075819 / 250000000000)) := by
  have h := reflection_log_1915_neg
  have he : Real.log (347943075819 / 250000000000) = -Real.log (250000000000 / 347943075819) := by
    rw [show ((347943075819 / 250000000000) : ℝ) = ((250000000000 / 347943075819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1916_neg : (33078349 / 100000000) ≤ -Real.log (500000000000 / 696029183113) ∧
    -Real.log (500000000000 / 696029183113) ≤ (330783491 / 1000000000) := by
  have h := checkLog_sound (w := (196029183113 / 1196029183113)) (n := 12)
    (lo := (33078349 / 100000000)) (hi := (330783491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696029183113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696029183113 / 500000000000) = 1/(500000000000 / 696029183113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1916 : Bounds (33078349 / 100000000) (330783491 / 1000000000) (Real.log (696029183113 / 500000000000)) := by
  have h := reflection_log_1916_neg
  have he : Real.log (696029183113 / 500000000000) = -Real.log (500000000000 / 696029183113) := by
    rw [show ((696029183113 / 500000000000) : ℝ) = ((500000000000 / 696029183113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1917_neg : (151862349 / 1000000000) ≤ -Real.log (250 / 291) ∧
    -Real.log (250 / 291) ≤ (3037247 / 20000000) := by
  have h := checkLog_sound (w := (41 / 541)) (n := 12)
    (lo := (151862349 / 1000000000)) (hi := (3037247 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291 / 250) = 1/(250 / 291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1917 : Bounds (151862349 / 1000000000) (3037247 / 20000000) (Real.log (291 / 250)) := by
  have h := reflection_log_1917_neg
  have he : Real.log (291 / 250) = -Real.log (250 / 291) := by
    rw [show ((291 / 250) : ℝ) = ((250 / 291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1918_neg : (35825333 / 200000000) ≤ -Real.log (209 / 250) ∧
    -Real.log (209 / 250) ≤ (89563333 / 500000000) := by
  have h := checkLog_sound (w := (41 / 459)) (n := 12)
    (lo := (35825333 / 200000000)) (hi := (89563333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 209) = 1/(209 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1918 : Bounds (-89563333 / 500000000) (-35825333 / 200000000) (Real.log (209 / 250)) := by
  have h := reflection_log_1918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1919_neg : (81993 / 500000000) ≤ -Real.log (250000 / 250041) ∧
    -Real.log (250000 / 250041) ≤ (163987 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 500041)) (n := 12)
    (lo := (81993 / 500000000)) (hi := (163987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250041 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250041 / 250000) = 1/(250000 / 250041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1919 : Bounds (81993 / 500000000) (163987 / 1000000000) (Real.log (250041 / 250000)) := by
  have h := reflection_log_1919_neg
  have he : Real.log (250041 / 250000) = -Real.log (250000 / 250041) := by
    rw [show ((250041 / 250000) : ℝ) = ((250000 / 250041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

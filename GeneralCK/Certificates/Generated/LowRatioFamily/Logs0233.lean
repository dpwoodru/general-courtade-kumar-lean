import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14912_neg : (969529 / 1000000000) ≤ -Real.log (100000 / 100097) ∧
    -Real.log (100000 / 100097) ≤ (96953 / 100000000) := by
  have h := checkLog_sound (w := (97 / 200097)) (n := 12)
    (lo := (969529 / 1000000000)) (hi := (96953 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100097 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100097 / 100000) = 1/(100000 / 100097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14912 : Bounds (969529 / 1000000000) (96953 / 100000000) (Real.log (100097 / 100000)) := by
  have h := reflection_log_14912_neg
  have he : Real.log (100097 / 100000) = -Real.log (100000 / 100097) := by
    rw [show ((100097 / 100000) : ℝ) = ((100000 / 100097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14913_neg : (97047 / 100000000) ≤ -Real.log (99903 / 100000) ∧
    -Real.log (99903 / 100000) ≤ (970471 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 199903)) (n := 12)
    (lo := (97047 / 100000000)) (hi := (970471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99903) = 1/(99903 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14913 : Bounds (-970471 / 1000000000) (-97047 / 100000000) (Real.log (99903 / 100000)) := by
  have h := reflection_log_14913_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14914_neg : (239393409 / 500000000) ≤ -Real.log (200000 / 322823) ∧
    -Real.log (200000 / 322823) ≤ (478786819 / 1000000000) := by
  have h := checkLog_sound (w := (122823 / 522823)) (n := 12)
    (lo := (239393409 / 500000000)) (hi := (478786819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322823 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322823 / 200000) = 1/(200000 / 322823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14914 : Bounds (239393409 / 500000000) (478786819 / 1000000000) (Real.log (322823 / 200000)) := by
  have h := reflection_log_14914_neg
  have he : Real.log (322823 / 200000) = -Real.log (200000 / 322823) := by
    rw [show ((322823 / 200000) : ℝ) = ((200000 / 322823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14915_neg : (23805397 / 25000000) ≤ -Real.log (77177 / 200000) ∧
    -Real.log (77177 / 200000) ≤ (476107941 / 500000000) := by
  have h := checkLog_sound (w := (22823 / 177177)) (n := 12)
    (lo := (2590687 / 10000000)) (hi := (259068701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 77177) = 1/(77177 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14915 : Bounds (-476107941 / 500000000) (-23805397 / 25000000) (Real.log (77177 / 200000)) := by
  have h := reflection_log_14915_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14916_neg : (239968007 / 500000000) ≤ -Real.log (1000000 / 1615971) ∧
    -Real.log (1000000 / 1615971) ≤ (95987203 / 200000000) := by
  have h := checkLog_sound (w := (615971 / 2615971)) (n := 12)
    (lo := (239968007 / 500000000)) (hi := (95987203 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1615971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1615971 / 1000000) = 1/(1000000 / 1615971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14916 : Bounds (239968007 / 500000000) (95987203 / 200000000) (Real.log (1615971 / 1000000)) := by
  have h := reflection_log_14916_neg
  have he : Real.log (1615971 / 1000000) = -Real.log (1000000 / 1615971) := by
    rw [show ((1615971 / 1000000) : ℝ) = ((1000000 / 1615971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14917_neg : (957037207 / 1000000000) ≤ -Real.log (384029 / 1000000) ∧
    -Real.log (384029 / 1000000) ≤ (957037209 / 1000000000) := by
  have h := checkLog_sound (w := (115971 / 884029)) (n := 12)
    (lo := (263890027 / 1000000000)) (hi := (65972507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 384029) = 1/(384029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14917 : Bounds (-957037209 / 1000000000) (-957037207 / 1000000000) (Real.log (384029 / 1000000)) := by
  have h := reflection_log_14917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14918_neg : (238550597 / 500000000) ≤ -Real.log (620579727159 / 1000000000000) ∧
    -Real.log (620579727159 / 1000000000000) ≤ (95420239 / 200000000) := by
  have h := checkLog_sound (w := (379420272841 / 1620579727159)) (n := 12)
    (lo := (238550597 / 500000000)) (hi := (95420239 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 620579727159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 620579727159) = 1/(620579727159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14918 : Bounds (-95420239 / 200000000) (-238550597 / 500000000) (Real.log (620579727159 / 1000000000000)) := by
  have h := reflection_log_14918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14919_neg : (236714531 / 500000000) ≤ -Real.log (24914510671 / 40000000000) ∧
    -Real.log (24914510671 / 40000000000) ≤ (473429063 / 1000000000) := by
  have h := checkLog_sound (w := (15085489329 / 64914510671)) (n := 12)
    (lo := (236714531 / 500000000)) (hi := (473429063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 24914510671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 24914510671) = 1/(24914510671 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14919 : Bounds (-473429063 / 1000000000) (-236714531 / 500000000) (Real.log (24914510671 / 40000000000)) := by
  have h := reflection_log_14919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14920_neg : (1431002699 / 1000000000) ≤ -Real.log (500000000000 / 2091445637949) ∧
    -Real.log (500000000000 / 2091445637949) ≤ (715501351 / 500000000) := by
  have h := checkLog_sound (w := (91445637949 / 4091445637949)) (n := 12)
    (lo := (44708339 / 1000000000)) (hi := (2235417 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2091445637949 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2091445637949 / 2000000000000) = 1/(500000000000 / 2091445637949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14920 : Bounds (1431002699 / 1000000000) (715501351 / 500000000) (Real.log (2091445637949 / 500000000000)) := by
  have h := reflection_log_14920_neg
  have he : Real.log (2091445637949 / 500000000000) = -Real.log (500000000000 / 2091445637949) := by
    rw [show ((2091445637949 / 500000000000) : ℝ) = ((500000000000 / 2091445637949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14921_neg : (1436973221 / 1000000000) ≤ -Real.log (250000000000 / 1051985006341) ∧
    -Real.log (250000000000 / 1051985006341) ≤ (179621653 / 125000000) := by
  have h := checkLog_sound (w := (51985006341 / 2051985006341)) (n := 12)
    (lo := (50678861 / 1000000000)) (hi := (25339431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1051985006341 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1051985006341 / 1000000000000) = 1/(250000000000 / 1051985006341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14921 : Bounds (1436973221 / 1000000000) (179621653 / 125000000) (Real.log (1051985006341 / 250000000000)) := by
  have h := reflection_log_14921_neg
  have he : Real.log (1051985006341 / 250000000000) = -Real.log (250000000000 / 1051985006341) := by
    rw [show ((1051985006341 / 250000000000) : ℝ) = ((250000000000 / 1051985006341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14922_neg : (4151293871 / 1000000000) ≤ -Real.log (500000000000 / 31758064516129) ∧
    -Real.log (500000000000 / 31758064516129) ≤ (4151293877 / 1000000000) := by
  have h := checkLog_sound (w := (15758064516129 / 47758064516129)) (n := 12)
    (lo := (685557971 / 1000000000)) (hi := (171389493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31758064516129 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31758064516129 / 16000000000000) = 1/(500000000000 / 31758064516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14922 : Bounds (4151293871 / 1000000000) (4151293877 / 1000000000) (Real.log (31758064516129 / 500000000000)) := by
  have h := reflection_log_14922_neg
  have he : Real.log (31758064516129 / 500000000000) = -Real.log (500000000000 / 31758064516129) := by
    rw [show ((31758064516129 / 500000000000) : ℝ) = ((500000000000 / 31758064516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14923_neg : (1046147859 / 250000000) ≤ -Real.log (250000000000 / 16416666666667) ∧
    -Real.log (250000000000 / 16416666666667) ≤ (4184591443 / 1000000000) := by
  have h := checkLog_sound (w := (416666666667 / 32416666666667)) (n := 12)
    (lo := (6427089 / 250000000)) (hi := (25708357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16416666666667 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(16416666666667 / 16000000000000) = 1/(250000000000 / 16416666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14923 : Bounds (1046147859 / 250000000) (4184591443 / 1000000000) (Real.log (16416666666667 / 250000000000)) := by
  have h := reflection_log_14923_neg
  have he : Real.log (16416666666667 / 250000000000) = -Real.log (250000000000 / 16416666666667) := by
    rw [show ((16416666666667 / 250000000000) : ℝ) = ((250000000000 / 16416666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14924_neg : (169635257 / 250000000) ≤ -Real.log (1000 / 1971) ∧
    -Real.log (1000 / 1971) ≤ (678541029 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 2971)) (n := 12)
    (lo := (169635257 / 250000000)) (hi := (678541029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971 / 1000) = 1/(1000 / 1971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14924 : Bounds (169635257 / 250000000) (678541029 / 1000000000) (Real.log (1971 / 1000)) := by
  have h := reflection_log_14924_neg
  have he : Real.log (1971 / 1000) = -Real.log (1000 / 1971) := by
    rw [show ((1971 / 1000) : ℝ) = ((1000 / 1971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14925_neg : (1770229723 / 500000000) ≤ -Real.log (29 / 1000) ∧
    -Real.log (29 / 1000) ≤ (885114863 / 250000000) := by
  have h := checkLog_sound (w := (9 / 241)) (n := 12)
    (lo := (37361773 / 500000000)) (hi := (74723547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 116) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 116) = 1/(29 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14925 : Bounds (-885114863 / 250000000) (-1770229723 / 500000000) (Real.log (29 / 1000)) := by
  have h := reflection_log_14925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14926_neg : (30329 / 31250000) ≤ -Real.log (1000000 / 1000971) ∧
    -Real.log (1000000 / 1000971) ≤ (970529 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 2000971)) (n := 12)
    (lo := (30329 / 31250000)) (hi := (970529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000971 / 1000000) = 1/(1000000 / 1000971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14926 : Bounds (30329 / 31250000) (970529 / 1000000000) (Real.log (1000971 / 1000000)) := by
  have h := reflection_log_14926_neg
  have he : Real.log (1000971 / 1000000) = -Real.log (1000000 / 1000971) := by
    rw [show ((1000971 / 1000000) : ℝ) = ((1000000 / 1000971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14927_neg : (971471 / 1000000000) ≤ -Real.log (999029 / 1000000) ∧
    -Real.log (999029 / 1000000) ≤ (60717 / 62500000) := by
  have h := checkLog_sound (w := (971 / 1999029)) (n := 12)
    (lo := (971471 / 1000000000)) (hi := (60717 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999029) = 1/(999029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14927 : Bounds (-60717 / 62500000) (-971471 / 1000000000) (Real.log (999029 / 1000000)) := by
  have h := reflection_log_14927_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14928_neg : (59941867 / 125000000) ≤ -Real.log (1000000 / 1615323) ∧
    -Real.log (1000000 / 1615323) ≤ (479534937 / 1000000000) := by
  have h := checkLog_sound (w := (615323 / 2615323)) (n := 12)
    (lo := (59941867 / 125000000)) (hi := (479534937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1615323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1615323 / 1000000) = 1/(1000000 / 1615323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14928 : Bounds (59941867 / 125000000) (479534937 / 1000000000) (Real.log (1615323 / 1000000)) := by
  have h := reflection_log_14928_neg
  have he : Real.log (1615323 / 1000000) = -Real.log (1000000 / 1615323) := by
    rw [show ((1615323 / 1000000) : ℝ) = ((1000000 / 1615323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14929_neg : (955351257 / 1000000000) ≤ -Real.log (384677 / 1000000) ∧
    -Real.log (384677 / 1000000) ≤ (955351259 / 1000000000) := by
  have h := checkLog_sound (w := (115323 / 884677)) (n := 12)
    (lo := (262204077 / 1000000000)) (hi := (131102039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 384677) = 1/(384677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14929 : Bounds (-955351259 / 1000000000) (-955351257 / 1000000000) (Real.log (384677 / 1000000)) := by
  have h := reflection_log_14929_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14930_neg : (480687601 / 1000000000) ≤ -Real.log (500000 / 808593) ∧
    -Real.log (500000 / 808593) ≤ (240343801 / 500000000) := by
  have h := checkLog_sound (w := (308593 / 1308593)) (n := 12)
    (lo := (480687601 / 1000000000)) (hi := (240343801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808593 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808593 / 500000) = 1/(500000 / 808593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14930 : Bounds (480687601 / 1000000000) (240343801 / 500000000) (Real.log (808593 / 500000)) := by
  have h := reflection_log_14930_neg
  have he : Real.log (808593 / 500000) = -Real.log (500000 / 808593) := by
    rw [show ((808593 / 500000) : ℝ) = ((500000 / 808593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14931_neg : (480103023 / 500000000) ≤ -Real.log (191407 / 500000) ∧
    -Real.log (191407 / 500000) ≤ (30006439 / 31250000) := by
  have h := checkLog_sound (w := (58593 / 441407)) (n := 12)
    (lo := (133529433 / 500000000)) (hi := (267058867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191407) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 191407) = 1/(191407 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14931 : Bounds (-30006439 / 31250000) (-480103023 / 500000000) (Real.log (191407 / 500000)) := by
  have h := reflection_log_14931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14932_neg : (95903689 / 200000000) ≤ -Real.log (154770360351 / 250000000000) ∧
    -Real.log (154770360351 / 250000000000) ≤ (239759223 / 500000000) := by
  have h := checkLog_sound (w := (95229639649 / 404770360351)) (n := 12)
    (lo := (95903689 / 200000000)) (hi := (239759223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 154770360351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 154770360351) = 1/(154770360351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14932 : Bounds (-239759223 / 500000000) (-95903689 / 200000000) (Real.log (154770360351 / 250000000000)) := by
  have h := reflection_log_14932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14933_neg : (475816321 / 1000000000) ≤ -Real.log (621377605671 / 1000000000000) ∧
    -Real.log (621377605671 / 1000000000000) ≤ (237908161 / 500000000) := by
  have h := checkLog_sound (w := (378622394329 / 1621377605671)) (n := 12)
    (lo := (475816321 / 1000000000)) (hi := (237908161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 621377605671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 621377605671) = 1/(621377605671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14933 : Bounds (-237908161 / 500000000) (-475816321 / 1000000000) (Real.log (621377605671 / 1000000000000)) := by
  have h := reflection_log_14933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14934_neg : (1434886193 / 1000000000) ≤ -Real.log (100000000000 / 419916709343) ∧
    -Real.log (100000000000 / 419916709343) ≤ (358721549 / 250000000) := by
  have h := checkLog_sound (w := (19916709343 / 819916709343)) (n := 12)
    (lo := (48591833 / 1000000000)) (hi := (24295917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419916709343 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(419916709343 / 400000000000) = 1/(100000000000 / 419916709343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14934 : Bounds (1434886193 / 1000000000) (358721549 / 250000000) (Real.log (419916709343 / 100000000000)) := by
  have h := reflection_log_14934_neg
  have he : Real.log (419916709343 / 100000000000) = -Real.log (100000000000 / 419916709343) := by
    rw [show ((419916709343 / 100000000000) : ℝ) = ((100000000000 / 419916709343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14935_neg : (90055853 / 62500000) ≤ -Real.log (100000000000 / 422446932453) ∧
    -Real.log (100000000000 / 422446932453) ≤ (1440893651 / 1000000000) := by
  have h := checkLog_sound (w := (22446932453 / 822446932453)) (n := 12)
    (lo := (6824911 / 125000000)) (hi := (54599289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422446932453 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(422446932453 / 400000000000) = 1/(100000000000 / 422446932453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14935 : Bounds (90055853 / 62500000) (1440893651 / 1000000000) (Real.log (422446932453 / 100000000000)) := by
  have h := reflection_log_14935_neg
  have he : Real.log (422446932453 / 100000000000) = -Real.log (100000000000 / 422446932453) := by
    rw [show ((422446932453 / 100000000000) : ℝ) = ((100000000000 / 422446932453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14936_neg : (1046147859 / 250000000) ≤ -Real.log (500000000000 / 32833333333333) ∧
    -Real.log (500000000000 / 32833333333333) ≤ (4184591443 / 1000000000) := by
  have h := checkLog_sound (w := (833333333333 / 64833333333333)) (n := 12)
    (lo := (6427089 / 250000000)) (hi := (25708357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32833333333333 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32833333333333 / 32000000000000) = 1/(500000000000 / 32833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14936 : Bounds (1046147859 / 250000000) (4184591443 / 1000000000) (Real.log (32833333333333 / 500000000000)) := by
  have h := reflection_log_14936_neg
  have he : Real.log (32833333333333 / 500000000000) = -Real.log (500000000000 / 32833333333333) := by
    rw [show ((32833333333333 / 500000000000) : ℝ) = ((500000000000 / 32833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14937_neg : (4219000473 / 1000000000) ≤ -Real.log (50000000000 / 3398275862069) ∧
    -Real.log (50000000000 / 3398275862069) ≤ (26368753 / 6250000) := by
  have h := checkLog_sound (w := (198275862069 / 6598275862069)) (n := 12)
    (lo := (60117393 / 1000000000)) (hi := (30058697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3398275862069 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3398275862069 / 3200000000000) = 1/(50000000000 / 3398275862069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14937 : Bounds (4219000473 / 1000000000) (26368753 / 6250000) (Real.log (3398275862069 / 50000000000)) := by
  have h := reflection_log_14937_neg
  have he : Real.log (3398275862069 / 50000000000) = -Real.log (50000000000 / 3398275862069) := by
    rw [show ((3398275862069 / 50000000000) : ℝ) = ((50000000000 / 3398275862069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14938_neg : (10610129 / 15625000) ≤ -Real.log (250 / 493) ∧
    -Real.log (250 / 493) ≤ (679048257 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 743)) (n := 12)
    (lo := (10610129 / 15625000)) (hi := (679048257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493 / 250) = 1/(250 / 493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14938 : Bounds (10610129 / 15625000) (679048257 / 1000000000) (Real.log (493 / 250)) := by
  have h := reflection_log_14938_neg
  have he : Real.log (493 / 250) = -Real.log (250 / 493) := by
    rw [show ((493 / 250) : ℝ) = ((250 / 493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14939_neg : (1787775383 / 500000000) ≤ -Real.log (7 / 250) ∧
    -Real.log (7 / 250) ≤ (893887693 / 250000000) := by
  have h := checkLog_sound (w := (13 / 237)) (n := 12)
    (lo := (54907433 / 500000000)) (hi := (109814867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 112) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 112) = 1/(7 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14939 : Bounds (-893887693 / 250000000) (-1787775383 / 500000000) (Real.log (7 / 250)) := by
  have h := reflection_log_14939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14940_neg : (971527 / 1000000000) ≤ -Real.log (250000 / 250243) ∧
    -Real.log (250000 / 250243) ≤ (121441 / 125000000) := by
  have h := checkLog_sound (w := (243 / 500243)) (n := 12)
    (lo := (971527 / 1000000000)) (hi := (121441 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250243 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250243 / 250000) = 1/(250000 / 250243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14940 : Bounds (971527 / 1000000000) (121441 / 125000000) (Real.log (250243 / 250000)) := by
  have h := reflection_log_14940_neg
  have he : Real.log (250243 / 250000) = -Real.log (250000 / 250243) := by
    rw [show ((250243 / 250000) : ℝ) = ((250000 / 250243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14941_neg : (121559 / 125000000) ≤ -Real.log (249757 / 250000) ∧
    -Real.log (249757 / 250000) ≤ (972473 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 499757)) (n := 12)
    (lo := (121559 / 125000000)) (hi := (972473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249757) = 1/(249757 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14941 : Bounds (-972473 / 1000000000) (-121559 / 125000000) (Real.log (249757 / 250000)) := by
  have h := reflection_log_14941_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14942_neg : (120071861 / 250000000) ≤ -Real.log (1000000 / 1616539) ∧
    -Real.log (1000000 / 1616539) ≤ (96057489 / 200000000) := by
  have h := checkLog_sound (w := (616539 / 2616539)) (n := 12)
    (lo := (120071861 / 250000000)) (hi := (96057489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1616539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1616539 / 1000000) = 1/(1000000 / 1616539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14942 : Bounds (120071861 / 250000000) (96057489 / 200000000) (Real.log (1616539 / 1000000)) := by
  have h := reflection_log_14942_neg
  have he : Real.log (1616539 / 1000000) = -Real.log (1000000 / 1616539) := by
    rw [show ((1616539 / 1000000) : ℝ) = ((1000000 / 1616539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14943_neg : (958517357 / 1000000000) ≤ -Real.log (383461 / 1000000) ∧
    -Real.log (383461 / 1000000) ≤ (958517359 / 1000000000) := by
  have h := checkLog_sound (w := (116539 / 883461)) (n := 12)
    (lo := (265370177 / 1000000000)) (hi := (132685089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383461) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 383461) = 1/(383461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14943 : Bounds (-958517359 / 1000000000) (-958517357 / 1000000000) (Real.log (383461 / 1000000)) := by
  have h := reflection_log_14943_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14944_neg : (481443567 / 1000000000) ≤ -Real.log (1000000 / 1618409) ∧
    -Real.log (1000000 / 1618409) ≤ (30090223 / 62500000) := by
  have h := checkLog_sound (w := (618409 / 2618409)) (n := 12)
    (lo := (481443567 / 1000000000)) (hi := (30090223 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1618409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1618409 / 1000000) = 1/(1000000 / 1618409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14944 : Bounds (481443567 / 1000000000) (30090223 / 62500000) (Real.log (1618409 / 1000000)) := by
  have h := reflection_log_14944_neg
  have he : Real.log (1618409 / 1000000) = -Real.log (1000000 / 1618409) := by
    rw [show ((1618409 / 1000000) : ℝ) = ((1000000 / 1618409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14945_neg : (240851481 / 250000000) ≤ -Real.log (381591 / 1000000) ∧
    -Real.log (381591 / 1000000) ≤ (481702963 / 500000000) := by
  have h := checkLog_sound (w := (118409 / 881591)) (n := 12)
    (lo := (33782343 / 125000000)) (hi := (54051749 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 381591) = 1/(381591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14945 : Bounds (-481702963 / 500000000) (-240851481 / 250000000) (Real.log (381591 / 1000000)) := by
  have h := reflection_log_14945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14946_neg : (120490589 / 250000000) ≤ -Real.log (617570308719 / 1000000000000) ∧
    -Real.log (617570308719 / 1000000000000) ≤ (481962357 / 1000000000) := by
  have h := checkLog_sound (w := (382429691281 / 1617570308719)) (n := 12)
    (lo := (120490589 / 250000000)) (hi := (481962357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 617570308719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 617570308719) = 1/(617570308719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14946 : Bounds (-481962357 / 1000000000) (-120490589 / 250000000) (Real.log (617570308719 / 1000000000000)) := by
  have h := reflection_log_14946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14947_neg : (239114957 / 500000000) ≤ -Real.log (619879661479 / 1000000000000) ∧
    -Real.log (619879661479 / 1000000000000) ≤ (95645983 / 200000000) := by
  have h := checkLog_sound (w := (380120338521 / 1619879661479)) (n := 12)
    (lo := (239114957 / 500000000)) (hi := (95645983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 619879661479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 619879661479) = 1/(619879661479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14947 : Bounds (-95645983 / 200000000) (-239114957 / 500000000) (Real.log (619879661479 / 1000000000000)) := by
  have h := reflection_log_14947_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14948_neg : (1438804801 / 1000000000) ≤ -Real.log (100000000000 / 421565426471) ∧
    -Real.log (100000000000 / 421565426471) ≤ (359701201 / 250000000) := by
  have h := checkLog_sound (w := (21565426471 / 821565426471)) (n := 12)
    (lo := (52510441 / 1000000000)) (hi := (26255221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421565426471 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(421565426471 / 400000000000) = 1/(100000000000 / 421565426471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14948 : Bounds (1438804801 / 1000000000) (359701201 / 250000000) (Real.log (421565426471 / 100000000000)) := by
  have h := reflection_log_14948_neg
  have he : Real.log (421565426471 / 100000000000) = -Real.log (100000000000 / 421565426471) := by
    rw [show ((421565426471 / 100000000000) : ℝ) = ((100000000000 / 421565426471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14949_neg : (1444849491 / 1000000000) ≤ -Real.log (250000000000 / 1060303440071) ∧
    -Real.log (250000000000 / 1060303440071) ≤ (722424747 / 500000000) := by
  have h := checkLog_sound (w := (60303440071 / 2060303440071)) (n := 12)
    (lo := (58555131 / 1000000000)) (hi := (14638783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1060303440071 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1060303440071 / 1000000000000) = 1/(250000000000 / 1060303440071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14949 : Bounds (1444849491 / 1000000000) (722424747 / 500000000) (Real.log (1060303440071 / 250000000000)) := by
  have h := reflection_log_14949_neg
  have he : Real.log (1060303440071 / 250000000000) = -Real.log (250000000000 / 1060303440071) := by
    rw [show ((1060303440071 / 250000000000) : ℝ) = ((250000000000 / 1060303440071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14950_neg : (4219000473 / 1000000000) ≤ -Real.log (500000000000 / 33982758620689) ∧
    -Real.log (500000000000 / 33982758620689) ≤ (26368753 / 6250000) := by
  have h := checkLog_sound (w := (1982758620689 / 65982758620689)) (n := 12)
    (lo := (60117393 / 1000000000)) (hi := (30058697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33982758620689 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33982758620689 / 32000000000000) = 1/(500000000000 / 33982758620689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14950 : Bounds (4219000473 / 1000000000) (26368753 / 6250000) (Real.log (33982758620689 / 500000000000)) := by
  have h := reflection_log_14950_neg
  have he : Real.log (33982758620689 / 500000000000) = -Real.log (500000000000 / 33982758620689) := by
    rw [show ((33982758620689 / 500000000000) : ℝ) = ((500000000000 / 33982758620689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14951_neg : (4254599021 / 1000000000) ≤ -Real.log (250000000000 / 17607142857143) ∧
    -Real.log (250000000000 / 17607142857143) ≤ (1063649757 / 250000000) := by
  have h := checkLog_sound (w := (1607142857143 / 33607142857143)) (n := 12)
    (lo := (95715941 / 1000000000)) (hi := (47857971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17607142857143 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17607142857143 / 16000000000000) = 1/(250000000000 / 17607142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14951 : Bounds (4254599021 / 1000000000) (1063649757 / 250000000) (Real.log (17607142857143 / 250000000000)) := by
  have h := reflection_log_14951_neg
  have he : Real.log (17607142857143 / 250000000000) = -Real.log (250000000000 / 17607142857143) := by
    rw [show ((17607142857143 / 250000000000) : ℝ) = ((250000000000 / 17607142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14952_neg : (679555227 / 1000000000) ≤ -Real.log (1000 / 1973) ∧
    -Real.log (1000 / 1973) ≤ (169888807 / 250000000) := by
  have h := checkLog_sound (w := (973 / 2973)) (n := 12)
    (lo := (679555227 / 1000000000)) (hi := (169888807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1973 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1973 / 1000) = 1/(1000 / 1973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14952 : Bounds (679555227 / 1000000000) (169888807 / 250000000) (Real.log (1973 / 1000)) := by
  have h := reflection_log_14952_neg
  have he : Real.log (1973 / 1000) = -Real.log (1000 / 1973) := by
    rw [show ((1973 / 1000) : ℝ) = ((1000 / 1973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14953_neg : (361191841 / 100000000) ≤ -Real.log (27 / 1000) ∧
    -Real.log (27 / 1000) ≤ (225744901 / 62500000) := by
  have h := checkLog_sound (w := (17 / 233)) (n := 12)
    (lo := (14618251 / 100000000)) (hi := (146182511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 108) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 108) = 1/(27 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14953 : Bounds (-225744901 / 62500000) (-361191841 / 100000000) (Real.log (27 / 1000)) := by
  have h := reflection_log_14953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14954_neg : (486263 / 500000000) ≤ -Real.log (1000000 / 1000973) ∧
    -Real.log (1000000 / 1000973) ≤ (972527 / 1000000000) := by
  have h := checkLog_sound (w := (973 / 2000973)) (n := 12)
    (lo := (486263 / 500000000)) (hi := (972527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000973 / 1000000) = 1/(1000000 / 1000973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14954 : Bounds (486263 / 500000000) (972527 / 1000000000) (Real.log (1000973 / 1000000)) := by
  have h := reflection_log_14954_neg
  have he : Real.log (1000973 / 1000000) = -Real.log (1000000 / 1000973) := by
    rw [show ((1000973 / 1000000) : ℝ) = ((1000000 / 1000973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14955_neg : (973473 / 1000000000) ≤ -Real.log (999027 / 1000000) ∧
    -Real.log (999027 / 1000000) ≤ (486737 / 500000000) := by
  have h := checkLog_sound (w := (973 / 1999027)) (n := 12)
    (lo := (973473 / 1000000000)) (hi := (486737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999027) = 1/(999027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14955 : Bounds (-486737 / 500000000) (-973473 / 1000000000) (Real.log (999027 / 1000000)) := by
  have h := reflection_log_14955_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14956_neg : (1879077 / 3906250) ≤ -Real.log (500000 / 808881) ∧
    -Real.log (500000 / 808881) ≤ (481043713 / 1000000000) := by
  have h := checkLog_sound (w := (308881 / 1308881)) (n := 12)
    (lo := (1879077 / 3906250)) (hi := (481043713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808881 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808881 / 500000) = 1/(500000 / 808881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14956 : Bounds (1879077 / 3906250) (481043713 / 1000000000) (Real.log (808881 / 500000)) := by
  have h := reflection_log_14956_neg
  have he : Real.log (808881 / 500000) = -Real.log (500000 / 808881) := by
    rw [show ((808881 / 500000) : ℝ) = ((500000 / 808881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14957_neg : (961711827 / 1000000000) ≤ -Real.log (191119 / 500000) ∧
    -Real.log (191119 / 500000) ≤ (961711829 / 1000000000) := by
  have h := checkLog_sound (w := (58881 / 441119)) (n := 12)
    (lo := (268564647 / 1000000000)) (hi := (33570581 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 191119) = 1/(191119 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14957 : Bounds (-961711829 / 1000000000) (-961711827 / 1000000000) (Real.log (191119 / 500000)) := by
  have h := reflection_log_14957_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14958_neg : (241101951 / 500000000) ≤ -Real.log (25000 / 40491) ∧
    -Real.log (25000 / 40491) ≤ (482203903 / 1000000000) := by
  have h := checkLog_sound (w := (15491 / 65491)) (n := 12)
    (lo := (241101951 / 500000000)) (hi := (482203903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40491 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40491 / 25000) = 1/(25000 / 40491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14958 : Bounds (241101951 / 500000000) (482203903 / 1000000000) (Real.log (40491 / 25000)) := by
  have h := reflection_log_14958_neg
  have he : Real.log (40491 / 25000) = -Real.log (25000 / 40491) := by
    rw [show ((40491 / 25000) : ℝ) = ((25000 / 40491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14959_neg : (193327421 / 200000000) ≤ -Real.log (9509 / 25000) ∧
    -Real.log (9509 / 25000) ≤ (966637107 / 1000000000) := by
  have h := checkLog_sound (w := (2991 / 22009)) (n := 12)
    (lo := (10939597 / 40000000)) (hi := (136744963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9509) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 9509) = 1/(9509 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14959 : Bounds (-966637107 / 1000000000) (-193327421 / 200000000) (Real.log (9509 / 25000)) := by
  have h := reflection_log_14959_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14960_neg : (484433203 / 1000000000) ≤ -Real.log (385028919 / 625000000) ∧
    -Real.log (385028919 / 625000000) ≤ (121108301 / 250000000) := by
  have h := checkLog_sound (w := (239971081 / 1010028919)) (n := 12)
    (lo := (484433203 / 1000000000)) (hi := (121108301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 385028919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 385028919) = 1/(385028919 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14960 : Bounds (-121108301 / 250000000) (-484433203 / 1000000000) (Real.log (385028919 / 625000000)) := by
  have h := reflection_log_14960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14961_neg : (96133623 / 200000000) ≤ -Real.log (154592527839 / 250000000000) ∧
    -Real.log (154592527839 / 250000000000) ≤ (120167029 / 250000000) := by
  have h := checkLog_sound (w := (95407472161 / 404592527839)) (n := 12)
    (lo := (96133623 / 200000000)) (hi := (120167029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 154592527839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 154592527839) = 1/(154592527839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14961 : Bounds (-120167029 / 250000000) (-96133623 / 200000000) (Real.log (154592527839 / 250000000000)) := by
  have h := reflection_log_14961_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14962_neg : (1442755539 / 1000000000) ≤ -Real.log (500000000000 / 2116171076659) ∧
    -Real.log (500000000000 / 2116171076659) ≤ (721377771 / 500000000) := by
  have h := checkLog_sound (w := (116171076659 / 4116171076659)) (n := 12)
    (lo := (56461179 / 1000000000)) (hi := (2823059 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2116171076659 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2116171076659 / 2000000000000) = 1/(500000000000 / 2116171076659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14962 : Bounds (1442755539 / 1000000000) (721377771 / 500000000) (Real.log (2116171076659 / 500000000000)) := by
  have h := reflection_log_14962_neg
  have he : Real.log (2116171076659 / 500000000000) = -Real.log (500000000000 / 2116171076659) := by
    rw [show ((2116171076659 / 500000000000) : ℝ) = ((500000000000 / 2116171076659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14963_neg : (1448841007 / 1000000000) ≤ -Real.log (250000000000 / 1064544116101) ∧
    -Real.log (250000000000 / 1064544116101) ≤ (144884101 / 100000000) := by
  have h := checkLog_sound (w := (64544116101 / 2064544116101)) (n := 12)
    (lo := (62546647 / 1000000000)) (hi := (7818331 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1064544116101 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1064544116101 / 1000000000000) = 1/(250000000000 / 1064544116101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14963 : Bounds (1448841007 / 1000000000) (144884101 / 100000000) (Real.log (1064544116101 / 250000000000)) := by
  have h := reflection_log_14963_neg
  have he : Real.log (1064544116101 / 250000000000) = -Real.log (250000000000 / 1064544116101) := by
    rw [show ((1064544116101 / 250000000000) : ℝ) = ((250000000000 / 1064544116101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14964_neg : (4254599021 / 1000000000) ≤ -Real.log (100000000000 / 7042857142857) ∧
    -Real.log (100000000000 / 7042857142857) ≤ (1063649757 / 250000000) := by
  have h := checkLog_sound (w := (642857142857 / 13442857142857)) (n := 12)
    (lo := (95715941 / 1000000000)) (hi := (47857971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7042857142857 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7042857142857 / 6400000000000) = 1/(100000000000 / 7042857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14964 : Bounds (4254599021 / 1000000000) (1063649757 / 250000000) (Real.log (7042857142857 / 100000000000)) := by
  have h := reflection_log_14964_neg
  have he : Real.log (7042857142857 / 100000000000) = -Real.log (100000000000 / 7042857142857) := by
    rw [show ((7042857142857 / 100000000000) : ℝ) = ((100000000000 / 7042857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14965_neg : (1072868409 / 250000000) ≤ -Real.log (250000000000 / 18268518518519) ∧
    -Real.log (250000000000 / 18268518518519) ≤ (4291473643 / 1000000000) := by
  have h := checkLog_sound (w := (2268518518519 / 34268518518519)) (n := 12)
    (lo := (33147639 / 250000000)) (hi := (132590557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18268518518519 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18268518518519 / 16000000000000) = 1/(250000000000 / 18268518518519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14965 : Bounds (1072868409 / 250000000) (4291473643 / 1000000000) (Real.log (18268518518519 / 250000000000)) := by
  have h := reflection_log_14965_neg
  have he : Real.log (18268518518519 / 250000000000) = -Real.log (250000000000 / 18268518518519) := by
    rw [show ((18268518518519 / 250000000000) : ℝ) = ((250000000000 / 18268518518519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14966_neg : (680061941 / 1000000000) ≤ -Real.log (500 / 987) ∧
    -Real.log (500 / 987) ≤ (340030971 / 500000000) := by
  have h := checkLog_sound (w := (487 / 1487)) (n := 12)
    (lo := (680061941 / 1000000000)) (hi := (340030971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987 / 500) = 1/(500 / 987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14966 : Bounds (680061941 / 1000000000) (340030971 / 500000000) (Real.log (987 / 500)) := by
  have h := reflection_log_14966_neg
  have he : Real.log (987 / 500) = -Real.log (500 / 987) := by
    rw [show ((987 / 500) : ℝ) = ((500 / 987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14967_neg : (1824829369 / 500000000) ≤ -Real.log (13 / 500) ∧
    -Real.log (13 / 500) ≤ (456207343 / 125000000) := by
  have h := checkLog_sound (w := (21 / 229)) (n := 12)
    (lo := (91961419 / 500000000)) (hi := (183922839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 104) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 104) = 1/(13 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14967 : Bounds (-456207343 / 125000000) (-1824829369 / 500000000) (Real.log (13 / 500)) := by
  have h := reflection_log_14967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14968_neg : (38941 / 40000000) ≤ -Real.log (500000 / 500487) ∧
    -Real.log (500000 / 500487) ≤ (486763 / 500000000) := by
  have h := checkLog_sound (w := (487 / 1000487)) (n := 12)
    (lo := (38941 / 40000000)) (hi := (486763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500487 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500487 / 500000) = 1/(500000 / 500487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14968 : Bounds (38941 / 40000000) (486763 / 500000000) (Real.log (500487 / 500000)) := by
  have h := reflection_log_14968_neg
  have he : Real.log (500487 / 500000) = -Real.log (500000 / 500487) := by
    rw [show ((500487 / 500000) : ℝ) = ((500000 / 500487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14969_neg : (487237 / 500000000) ≤ -Real.log (499513 / 500000) ∧
    -Real.log (499513 / 500000) ≤ (38979 / 40000000) := by
  have h := checkLog_sound (w := (487 / 999513)) (n := 12)
    (lo := (487237 / 500000000)) (hi := (38979 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499513) = 1/(499513 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14969 : Bounds (-38979 / 40000000) (-487237 / 500000000) (Real.log (499513 / 500000)) := by
  have h := reflection_log_14969_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14970_neg : (60225621 / 125000000) ≤ -Real.log (500000 / 809497) ∧
    -Real.log (500000 / 809497) ≤ (481804969 / 1000000000) := by
  have h := checkLog_sound (w := (309497 / 1309497)) (n := 12)
    (lo := (60225621 / 125000000)) (hi := (481804969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809497 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(809497 / 500000) = 1/(500000 / 809497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14970 : Bounds (60225621 / 125000000) (481804969 / 1000000000) (Real.log (809497 / 500000)) := by
  have h := reflection_log_14970_neg
  have he : Real.log (809497 / 500000) = -Real.log (500000 / 809497) := by
    rw [show ((809497 / 500000) : ℝ) = ((500000 / 809497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14971_neg : (192988031 / 200000000) ≤ -Real.log (190503 / 500000) ∧
    -Real.log (190503 / 500000) ≤ (964940157 / 1000000000) := by
  have h := checkLog_sound (w := (59497 / 440503)) (n := 12)
    (lo := (10871719 / 40000000)) (hi := (16987061 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190503) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 190503) = 1/(190503 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14971 : Bounds (-964940157 / 1000000000) (-192988031 / 200000000) (Real.log (190503 / 500000)) := by
  have h := reflection_log_14971_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14972_neg : (482969211 / 1000000000) ≤ -Real.log (12500 / 20261) ∧
    -Real.log (12500 / 20261) ≤ (120742303 / 250000000) := by
  have h := checkLog_sound (w := (7761 / 32761)) (n := 12)
    (lo := (482969211 / 1000000000)) (hi := (120742303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20261 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20261 / 12500) = 1/(12500 / 20261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14972 : Bounds (482969211 / 1000000000) (120742303 / 250000000) (Real.log (20261 / 12500)) := by
  have h := reflection_log_14972_neg
  have he : Real.log (20261 / 12500) = -Real.log (12500 / 20261) := by
    rw [show ((20261 / 12500) : ℝ) = ((12500 / 20261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14973_neg : (387961 / 400000) ≤ -Real.log (4739 / 12500) ∧
    -Real.log (4739 / 12500) ≤ (484951251 / 500000000) := by
  have h := checkLog_sound (w := (1511 / 10989)) (n := 12)
    (lo := (6918883 / 25000000)) (hi := (276755321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4739) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6250 / 4739) = 1/(4739 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14973 : Bounds (-484951251 / 500000000) (-387961 / 400000) (Real.log (4739 / 12500)) := by
  have h := reflection_log_14973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14974_neg : (486933289 / 1000000000) ≤ -Real.log (96016879 / 156250000) ∧
    -Real.log (96016879 / 156250000) ≤ (48693329 / 100000000) := by
  have h := checkLog_sound (w := (60233121 / 252266879)) (n := 12)
    (lo := (486933289 / 1000000000)) (hi := (48693329 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 96016879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 96016879) = 1/(96016879 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14974 : Bounds (-48693329 / 100000000) (-486933289 / 1000000000) (Real.log (96016879 / 156250000)) := by
  have h := reflection_log_14974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14975_neg : (483135187 / 1000000000) ≤ -Real.log (154211606991 / 250000000000) ∧
    -Real.log (154211606991 / 250000000000) ≤ (120783797 / 250000000) := by
  have h := checkLog_sound (w := (95788393009 / 404211606991)) (n := 12)
    (lo := (483135187 / 1000000000)) (hi := (120783797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 154211606991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 154211606991) = 1/(154211606991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14975 : Bounds (-120783797 / 250000000) (-483135187 / 1000000000) (Real.log (154211606991 / 250000000000)) := by
  have h := reflection_log_14975_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

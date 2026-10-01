import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12992_neg : (138712827 / 500000000) ≤ -Real.log (62500 / 82483) ∧
    -Real.log (62500 / 82483) ≤ (55485131 / 200000000) := by
  have h := checkLog_sound (w := (19983 / 144983)) (n := 12)
    (lo := (138712827 / 500000000)) (hi := (55485131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82483 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82483 / 62500) = 1/(62500 / 82483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12992 : Bounds (138712827 / 500000000) (55485131 / 200000000) (Real.log (82483 / 62500)) := by
  have h := reflection_log_12992_neg
  have he : Real.log (82483 / 62500) = -Real.log (62500 / 82483) := by
    rw [show ((82483 / 62500) : ℝ) = ((62500 / 82483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12993_neg : (2407891 / 6250000) ≤ -Real.log (42517 / 62500) ∧
    -Real.log (42517 / 62500) ≤ (385262561 / 1000000000) := by
  have h := checkLog_sound (w := (19983 / 105017)) (n := 12)
    (lo := (2407891 / 6250000)) (hi := (385262561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42517) = 1/(42517 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12993 : Bounds (-385262561 / 1000000000) (-2407891 / 6250000) (Real.log (42517 / 62500)) := by
  have h := reflection_log_12993_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12994_neg : (53918453 / 500000000) ≤ -Real.log (3506929711 / 3906250000) ∧
    -Real.log (3506929711 / 3906250000) ≤ (107836907 / 1000000000) := by
  have h := checkLog_sound (w := (399320289 / 7413179711)) (n := 12)
    (lo := (53918453 / 500000000)) (hi := (107836907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3506929711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3506929711) = 1/(3506929711 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12994 : Bounds (-107836907 / 1000000000) (-53918453 / 500000000) (Real.log (3506929711 / 3906250000)) := by
  have h := reflection_log_12994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12995_neg : (3316751 / 31250000) ≤ -Real.log (899302305759 / 1000000000000) ∧
    -Real.log (899302305759 / 1000000000000) ≤ (106136033 / 1000000000) := by
  have h := checkLog_sound (w := (100697694241 / 1899302305759)) (n := 12)
    (lo := (3316751 / 31250000)) (hi := (106136033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 899302305759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 899302305759) = 1/(899302305759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12995 : Bounds (-106136033 / 1000000000) (-3316751 / 31250000) (Real.log (899302305759 / 1000000000000)) := by
  have h := reflection_log_12995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12996_neg : (131469687 / 200000000) ≤ -Real.log (250000000000 / 482417225867) ∧
    -Real.log (250000000000 / 482417225867) ≤ (164337109 / 250000000) := by
  have h := checkLog_sound (w := (232417225867 / 732417225867)) (n := 12)
    (lo := (131469687 / 200000000)) (hi := (164337109 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((482417225867 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(482417225867 / 250000000000) = 1/(250000000000 / 482417225867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12996 : Bounds (131469687 / 200000000) (164337109 / 250000000) (Real.log (482417225867 / 250000000000)) := by
  have h := reflection_log_12996_neg
  have he : Real.log (482417225867 / 250000000000) = -Real.log (250000000000 / 482417225867) := by
    rw [show ((482417225867 / 250000000000) : ℝ) = ((250000000000 / 482417225867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12997_neg : (132537643 / 200000000) ≤ -Real.log (500000000000 / 970000235201) ∧
    -Real.log (500000000000 / 970000235201) ≤ (82836027 / 125000000) := by
  have h := checkLog_sound (w := (470000235201 / 1470000235201)) (n := 12)
    (lo := (132537643 / 200000000)) (hi := (82836027 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970000235201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970000235201 / 500000000000) = 1/(500000000000 / 970000235201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12997 : Bounds (132537643 / 200000000) (82836027 / 125000000) (Real.log (970000235201 / 500000000000)) := by
  have h := reflection_log_12997_neg
  have he : Real.log (970000235201 / 500000000000) = -Real.log (500000000000 / 970000235201) := by
    rw [show ((970000235201 / 500000000000) : ℝ) = ((500000000000 / 970000235201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12998_neg : (1364561123 / 1000000000) ≤ -Real.log (250000000000 / 978501228501) ∧
    -Real.log (250000000000 / 978501228501) ≤ (10916489 / 8000000) := by
  have h := checkLog_sound (w := (478501228501 / 1478501228501)) (n := 12)
    (lo := (671413943 / 1000000000)) (hi := (83926743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978501228501 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(978501228501 / 500000000000) = 1/(250000000000 / 978501228501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12998 : Bounds (1364561123 / 1000000000) (10916489 / 8000000) (Real.log (978501228501 / 250000000000)) := by
  have h := reflection_log_12998_neg
  have he : Real.log (978501228501 / 250000000000) = -Real.log (250000000000 / 978501228501) := by
    rw [show ((978501228501 / 250000000000) : ℝ) = ((250000000000 / 978501228501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12999_neg : (1373840899 / 1000000000) ≤ -Real.log (500000000000 / 1975247524753) ∧
    -Real.log (500000000000 / 1975247524753) ≤ (1373840901 / 1000000000) := by
  have h := checkLog_sound (w := (975247524753 / 2975247524753)) (n := 12)
    (lo := (680693719 / 1000000000)) (hi := (17017343 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975247524753 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1975247524753 / 1000000000000) = 1/(500000000000 / 1975247524753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12999 : Bounds (1373840899 / 1000000000) (1373840901 / 1000000000) (Real.log (1975247524753 / 500000000000)) := by
  have h := reflection_log_12999_neg
  have he : Real.log (1975247524753 / 500000000000) = -Real.log (500000000000 / 1975247524753) := by
    rw [show ((1975247524753 / 500000000000) : ℝ) = ((500000000000 / 1975247524753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13000_neg : (469378433 / 1000000000) ≤ -Real.log (1000 / 1599) ∧
    -Real.log (1000 / 1599) ≤ (234689217 / 500000000) := by
  have h := checkLog_sound (w := (599 / 2599)) (n := 12)
    (lo := (469378433 / 1000000000)) (hi := (234689217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1599 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1599 / 1000) = 1/(1000 / 1599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13000 : Bounds (469378433 / 1000000000) (234689217 / 500000000) (Real.log (1599 / 1000)) := by
  have h := reflection_log_13000_neg
  have he : Real.log (1599 / 1000) = -Real.log (1000 / 1599) := by
    rw [show ((1599 / 1000) : ℝ) = ((1000 / 1599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13001_neg : (913793851 / 1000000000) ≤ -Real.log (401 / 1000) ∧
    -Real.log (401 / 1000) ≤ (913793853 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 901)) (n := 12)
    (lo := (220646671 / 1000000000)) (hi := (13790417 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 401) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 401) = 1/(401 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13001 : Bounds (-913793853 / 1000000000) (-913793851 / 1000000000) (Real.log (401 / 1000)) := by
  have h := reflection_log_13001_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13002_neg : (29941 / 50000000) ≤ -Real.log (1000000 / 1000599) ∧
    -Real.log (1000000 / 1000599) ≤ (598821 / 1000000000) := by
  have h := checkLog_sound (w := (599 / 2000599)) (n := 12)
    (lo := (29941 / 50000000)) (hi := (598821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000599 / 1000000) = 1/(1000000 / 1000599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13002 : Bounds (29941 / 50000000) (598821 / 1000000000) (Real.log (1000599 / 1000000)) := by
  have h := reflection_log_13002_neg
  have he : Real.log (1000599 / 1000000) = -Real.log (1000000 / 1000599) := by
    rw [show ((1000599 / 1000000) : ℝ) = ((1000000 / 1000599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13003_neg : (599179 / 1000000000) ≤ -Real.log (999401 / 1000000) ∧
    -Real.log (999401 / 1000000) ≤ (29959 / 50000000) := by
  have h := checkLog_sound (w := (599 / 1999401)) (n := 12)
    (lo := (599179 / 1000000000)) (hi := (29959 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999401) = 1/(999401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13003 : Bounds (-29959 / 50000000) (-599179 / 1000000000) (Real.log (999401 / 1000000)) := by
  have h := reflection_log_13003_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13004_neg : (277009573 / 1000000000) ≤ -Real.log (1000000 / 1319179) ∧
    -Real.log (1000000 / 1319179) ≤ (138504787 / 500000000) := by
  have h := checkLog_sound (w := (319179 / 2319179)) (n := 12)
    (lo := (277009573 / 1000000000)) (hi := (138504787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319179 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319179 / 1000000) = 1/(1000000 / 1319179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13004 : Bounds (277009573 / 1000000000) (138504787 / 500000000) (Real.log (1319179 / 1000000)) := by
  have h := reflection_log_13004_neg
  have he : Real.log (1319179 / 1000000) = -Real.log (1000000 / 1319179) := by
    rw [show ((1319179 / 1000000) : ℝ) = ((1000000 / 1319179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13005_neg : (24028491 / 62500000) ≤ -Real.log (680821 / 1000000) ∧
    -Real.log (680821 / 1000000) ≤ (384455857 / 1000000000) := by
  have h := checkLog_sound (w := (319179 / 1680821)) (n := 12)
    (lo := (24028491 / 62500000)) (hi := (384455857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 680821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 680821) = 1/(680821 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13005 : Bounds (-384455857 / 1000000000) (-24028491 / 62500000) (Real.log (680821 / 1000000)) := by
  have h := reflection_log_13005_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13006_neg : (278831017 / 1000000000) ≤ -Real.log (62500 / 82599) ∧
    -Real.log (62500 / 82599) ≤ (139415509 / 500000000) := by
  have h := checkLog_sound (w := (20099 / 145099)) (n := 12)
    (lo := (278831017 / 1000000000)) (hi := (139415509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82599 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82599 / 62500) = 1/(62500 / 82599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13006 : Bounds (278831017 / 1000000000) (139415509 / 500000000) (Real.log (82599 / 62500)) := by
  have h := reflection_log_13006_neg
  have he : Real.log (82599 / 62500) = -Real.log (62500 / 82599) := by
    rw [show ((82599 / 62500) : ℝ) = ((62500 / 82599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13007_neg : (387994609 / 1000000000) ≤ -Real.log (42401 / 62500) ∧
    -Real.log (42401 / 62500) ≤ (38799461 / 100000000) := by
  have h := checkLog_sound (w := (20099 / 104901)) (n := 12)
    (lo := (387994609 / 1000000000)) (hi := (38799461 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42401) = 1/(42401 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13007 : Bounds (-38799461 / 100000000) (-387994609 / 1000000000) (Real.log (42401 / 62500)) := by
  have h := reflection_log_13007_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13008_neg : (13645449 / 125000000) ≤ -Real.log (3502280199 / 3906250000) ∧
    -Real.log (3502280199 / 3906250000) ≤ (109163593 / 1000000000) := by
  have h := checkLog_sound (w := (403969801 / 7408530199)) (n := 12)
    (lo := (13645449 / 125000000)) (hi := (109163593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3502280199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3502280199) = 1/(3502280199 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13008 : Bounds (-109163593 / 1000000000) (-13645449 / 125000000) (Real.log (3502280199 / 3906250000)) := by
  have h := reflection_log_13008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13009_neg : (53723141 / 500000000) ≤ -Real.log (898124765959 / 1000000000000) ∧
    -Real.log (898124765959 / 1000000000000) ≤ (107446283 / 1000000000) := by
  have h := checkLog_sound (w := (101875234041 / 1898124765959)) (n := 12)
    (lo := (53723141 / 500000000)) (hi := (107446283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 898124765959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 898124765959) = 1/(898124765959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13009 : Bounds (-107446283 / 1000000000) (-53723141 / 500000000) (Real.log (898124765959 / 1000000000000)) := by
  have h := reflection_log_13009_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13010_neg : (661465429 / 1000000000) ≤ -Real.log (125000000000 / 242203714339) ∧
    -Real.log (125000000000 / 242203714339) ≤ (66146543 / 100000000) := by
  have h := checkLog_sound (w := (117203714339 / 367203714339)) (n := 12)
    (lo := (661465429 / 1000000000)) (hi := (66146543 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242203714339 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242203714339 / 125000000000) = 1/(125000000000 / 242203714339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13010 : Bounds (661465429 / 1000000000) (66146543 / 100000000) (Real.log (242203714339 / 125000000000)) := by
  have h := reflection_log_13010_neg
  have he : Real.log (242203714339 / 125000000000) = -Real.log (125000000000 / 242203714339) := by
    rw [show ((242203714339 / 125000000000) : ℝ) = ((125000000000 / 242203714339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13011_neg : (666825627 / 1000000000) ≤ -Real.log (125000000000 / 243505459777) ∧
    -Real.log (125000000000 / 243505459777) ≤ (166706407 / 250000000) := by
  have h := checkLog_sound (w := (118505459777 / 368505459777)) (n := 12)
    (lo := (666825627 / 1000000000)) (hi := (166706407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243505459777 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243505459777 / 125000000000) = 1/(125000000000 / 243505459777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13011 : Bounds (666825627 / 1000000000) (166706407 / 250000000) (Real.log (243505459777 / 125000000000)) := by
  have h := reflection_log_13011_neg
  have he : Real.log (243505459777 / 125000000000) = -Real.log (125000000000 / 243505459777) := by
    rw [show ((243505459777 / 125000000000) : ℝ) = ((125000000000 / 243505459777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13012_neg : (1373840899 / 1000000000) ≤ -Real.log (31250000000 / 123452970297) ∧
    -Real.log (31250000000 / 123452970297) ≤ (1373840901 / 1000000000) := by
  have h := checkLog_sound (w := (60952970297 / 185952970297)) (n := 12)
    (lo := (680693719 / 1000000000)) (hi := (17017343 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123452970297 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(123452970297 / 62500000000) = 1/(31250000000 / 123452970297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13012 : Bounds (1373840899 / 1000000000) (1373840901 / 1000000000) (Real.log (123452970297 / 31250000000)) := by
  have h := reflection_log_13012_neg
  have he : Real.log (123452970297 / 31250000000) = -Real.log (31250000000 / 123452970297) := by
    rw [show ((123452970297 / 31250000000) : ℝ) = ((31250000000 / 123452970297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13013_neg : (345793071 / 250000000) ≤ -Real.log (100000000000 / 398753117207) ∧
    -Real.log (100000000000 / 398753117207) ≤ (691586143 / 500000000) := by
  have h := checkLog_sound (w := (198753117207 / 598753117207)) (n := 12)
    (lo := (43126569 / 62500000)) (hi := (138005021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398753117207 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(398753117207 / 200000000000) = 1/(100000000000 / 398753117207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13013 : Bounds (345793071 / 250000000) (691586143 / 500000000) (Real.log (398753117207 / 100000000000)) := by
  have h := reflection_log_13013_neg
  have he : Real.log (398753117207 / 100000000000) = -Real.log (100000000000 / 398753117207) := by
    rw [show ((398753117207 / 100000000000) : ℝ) = ((100000000000 / 398753117207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13014_neg : (29453303 / 62500000) ≤ -Real.log (500 / 801) ∧
    -Real.log (500 / 801) ≤ (471252849 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 1301)) (n := 12)
    (lo := (29453303 / 62500000)) (hi := (471252849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801 / 500) = 1/(500 / 801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13014 : Bounds (29453303 / 62500000) (471252849 / 1000000000) (Real.log (801 / 500)) := by
  have h := reflection_log_13014_neg
  have he : Real.log (801 / 500) = -Real.log (500 / 801) := by
    rw [show ((801 / 500) : ℝ) = ((500 / 801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13015_neg : (921303273 / 1000000000) ≤ -Real.log (199 / 500) ∧
    -Real.log (199 / 500) ≤ (36852131 / 40000000) := by
  have h := checkLog_sound (w := (51 / 449)) (n := 12)
    (lo := (228156093 / 1000000000)) (hi := (114078047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 199) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 199) = 1/(199 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13015 : Bounds (-36852131 / 40000000) (-921303273 / 1000000000) (Real.log (199 / 500)) := by
  have h := reflection_log_13015_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13016_neg : (300909 / 500000000) ≤ -Real.log (500000 / 500301) ∧
    -Real.log (500000 / 500301) ≤ (601819 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 1000301)) (n := 12)
    (lo := (300909 / 500000000)) (hi := (601819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500301 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500301 / 500000) = 1/(500000 / 500301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13016 : Bounds (300909 / 500000000) (601819 / 1000000000) (Real.log (500301 / 500000)) := by
  have h := reflection_log_13016_neg
  have he : Real.log (500301 / 500000) = -Real.log (500000 / 500301) := by
    rw [show ((500301 / 500000) : ℝ) = ((500000 / 500301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13017_neg : (602181 / 1000000000) ≤ -Real.log (499699 / 500000) ∧
    -Real.log (499699 / 500000) ≤ (301091 / 500000000) := by
  have h := checkLog_sound (w := (301 / 999699)) (n := 12)
    (lo := (602181 / 1000000000)) (hi := (301091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499699) = 1/(499699 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13017 : Bounds (-301091 / 500000000) (-602181 / 1000000000) (Real.log (499699 / 500000)) := by
  have h := reflection_log_13017_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13018_neg : (278413249 / 1000000000) ≤ -Real.log (125000 / 165129) ∧
    -Real.log (125000 / 165129) ≤ (1113653 / 4000000) := by
  have h := checkLog_sound (w := (40129 / 290129)) (n := 12)
    (lo := (278413249 / 1000000000)) (hi := (1113653 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165129 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165129 / 125000) = 1/(125000 / 165129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13018 : Bounds (278413249 / 1000000000) (1113653 / 4000000) (Real.log (165129 / 125000)) := by
  have h := reflection_log_13018_neg
  have he : Real.log (165129 / 125000) = -Real.log (125000 / 165129) := by
    rw [show ((165129 / 125000) : ℝ) = ((125000 / 165129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13019_neg : (2419883 / 6250000) ≤ -Real.log (84871 / 125000) ∧
    -Real.log (84871 / 125000) ≤ (387181281 / 1000000000) := by
  have h := checkLog_sound (w := (40129 / 209871)) (n := 12)
    (lo := (2419883 / 6250000)) (hi := (387181281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84871) = 1/(84871 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13019 : Bounds (-387181281 / 1000000000) (-2419883 / 6250000) (Real.log (84871 / 125000)) := by
  have h := reflection_log_13019_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13020_neg : (280237429 / 1000000000) ≤ -Real.log (250000 / 330861) ∧
    -Real.log (250000 / 330861) ≤ (28023743 / 100000000) := by
  have h := checkLog_sound (w := (80861 / 580861)) (n := 12)
    (lo := (280237429 / 1000000000)) (hi := (28023743 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330861 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330861 / 250000) = 1/(250000 / 330861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13020 : Bounds (280237429 / 1000000000) (28023743 / 100000000) (Real.log (330861 / 250000)) := by
  have h := reflection_log_13020_neg
  have he : Real.log (330861 / 250000) = -Real.log (250000 / 330861) := by
    rw [show ((330861 / 250000) : ℝ) = ((250000 / 330861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13021_neg : (78148011 / 200000000) ≤ -Real.log (169139 / 250000) ∧
    -Real.log (169139 / 250000) ≤ (48842507 / 125000000) := by
  have h := checkLog_sound (w := (80861 / 419139)) (n := 12)
    (lo := (78148011 / 200000000)) (hi := (48842507 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 169139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 169139) = 1/(169139 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13021 : Bounds (-48842507 / 125000000) (-78148011 / 200000000) (Real.log (169139 / 250000)) := by
  have h := reflection_log_13021_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13022_neg : (55251313 / 500000000) ≤ -Real.log (55961498679 / 62500000000) ∧
    -Real.log (55961498679 / 62500000000) ≤ (110502627 / 1000000000) := by
  have h := checkLog_sound (w := (6538501321 / 118461498679)) (n := 12)
    (lo := (55251313 / 500000000)) (hi := (110502627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 55961498679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 55961498679) = 1/(55961498679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13022 : Bounds (-110502627 / 1000000000) (-55251313 / 500000000) (Real.log (55961498679 / 62500000000)) := by
  have h := reflection_log_13022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13023_neg : (108768031 / 1000000000) ≤ -Real.log (14014663359 / 15625000000) ∧
    -Real.log (14014663359 / 15625000000) ≤ (3399001 / 31250000) := by
  have h := checkLog_sound (w := (1610336641 / 29639663359)) (n := 12)
    (lo := (108768031 / 1000000000)) (hi := (3399001 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14014663359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14014663359) = 1/(14014663359 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13023 : Bounds (-3399001 / 31250000) (-108768031 / 1000000000) (Real.log (14014663359 / 15625000000)) := by
  have h := reflection_log_13023_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13024_neg : (665594529 / 1000000000) ≤ -Real.log (31250000000 / 60801466343) ∧
    -Real.log (31250000000 / 60801466343) ≤ (66559453 / 100000000) := by
  have h := checkLog_sound (w := (29551466343 / 92051466343)) (n := 12)
    (lo := (665594529 / 1000000000)) (hi := (66559453 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60801466343 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60801466343 / 31250000000) = 1/(31250000000 / 60801466343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13024 : Bounds (665594529 / 1000000000) (66559453 / 100000000) (Real.log (60801466343 / 31250000000)) := by
  have h := reflection_log_13024_neg
  have he : Real.log (60801466343 / 31250000000) = -Real.log (31250000000 / 60801466343) := by
    rw [show ((60801466343 / 31250000000) : ℝ) = ((31250000000 / 60801466343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13025_neg : (134195497 / 200000000) ≤ -Real.log (250000000000 / 489037123313) ∧
    -Real.log (250000000000 / 489037123313) ≤ (335488743 / 500000000) := by
  have h := checkLog_sound (w := (239037123313 / 739037123313)) (n := 12)
    (lo := (134195497 / 200000000)) (hi := (335488743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489037123313 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489037123313 / 250000000000) = 1/(250000000000 / 489037123313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13025 : Bounds (134195497 / 200000000) (335488743 / 500000000) (Real.log (489037123313 / 250000000000)) := by
  have h := reflection_log_13025_neg
  have he : Real.log (489037123313 / 250000000000) = -Real.log (250000000000 / 489037123313) := by
    rw [show ((489037123313 / 250000000000) : ℝ) = ((250000000000 / 489037123313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13026_neg : (345793071 / 250000000) ≤ -Real.log (250000000000 / 996882793017) ∧
    -Real.log (250000000000 / 996882793017) ≤ (691586143 / 500000000) := by
  have h := checkLog_sound (w := (496882793017 / 1496882793017)) (n := 12)
    (lo := (43126569 / 62500000)) (hi := (138005021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((996882793017 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(996882793017 / 500000000000) = 1/(250000000000 / 996882793017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13026 : Bounds (345793071 / 250000000) (691586143 / 500000000) (Real.log (996882793017 / 250000000000)) := by
  have h := reflection_log_13026_neg
  have he : Real.log (996882793017 / 250000000000) = -Real.log (250000000000 / 996882793017) := by
    rw [show ((996882793017 / 250000000000) : ℝ) = ((250000000000 / 996882793017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13027_neg : (1392556121 / 1000000000) ≤ -Real.log (500000000000 / 2012562814071) ∧
    -Real.log (500000000000 / 2012562814071) ≤ (348139031 / 250000000) := by
  have h := checkLog_sound (w := (12562814071 / 4012562814071)) (n := 12)
    (lo := (6261761 / 1000000000)) (hi := (3130881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2012562814071 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2012562814071 / 2000000000000) = 1/(500000000000 / 2012562814071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13027 : Bounds (1392556121 / 1000000000) (348139031 / 250000000) (Real.log (2012562814071 / 500000000000)) := by
  have h := reflection_log_13027_neg
  have he : Real.log (2012562814071 / 500000000000) = -Real.log (500000000000 / 2012562814071) := by
    rw [show ((2012562814071 / 500000000000) : ℝ) = ((500000000000 / 2012562814071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13028_neg : (118280939 / 250000000) ≤ -Real.log (200 / 321) ∧
    -Real.log (200 / 321) ≤ (473123757 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 521)) (n := 12)
    (lo := (118280939 / 250000000)) (hi := (473123757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321 / 200) = 1/(200 / 321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13028 : Bounds (118280939 / 250000000) (473123757 / 1000000000) (Real.log (321 / 200)) := by
  have h := reflection_log_13028_neg
  have he : Real.log (321 / 200) = -Real.log (200 / 321) := by
    rw [show ((321 / 200) : ℝ) = ((200 / 321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13029_neg : (928869513 / 1000000000) ≤ -Real.log (79 / 200) ∧
    -Real.log (79 / 200) ≤ (185773903 / 200000000) := by
  have h := checkLog_sound (w := (21 / 179)) (n := 12)
    (lo := (235722333 / 1000000000)) (hi := (117861167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 79) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 79) = 1/(79 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13029 : Bounds (-185773903 / 200000000) (-928869513 / 1000000000) (Real.log (79 / 200)) := by
  have h := reflection_log_13029_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13030_neg : (604817 / 1000000000) ≤ -Real.log (200000 / 200121) ∧
    -Real.log (200000 / 200121) ≤ (302409 / 500000000) := by
  have h := checkLog_sound (w := (121 / 400121)) (n := 12)
    (lo := (604817 / 1000000000)) (hi := (302409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200121 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200121 / 200000) = 1/(200000 / 200121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13030 : Bounds (604817 / 1000000000) (302409 / 500000000) (Real.log (200121 / 200000)) := by
  have h := reflection_log_13030_neg
  have he : Real.log (200121 / 200000) = -Real.log (200000 / 200121) := by
    rw [show ((200121 / 200000) : ℝ) = ((200000 / 200121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13031_neg : (605183 / 1000000000) ≤ -Real.log (199879 / 200000) ∧
    -Real.log (199879 / 200000) ≤ (1182 / 1953125) := by
  have h := checkLog_sound (w := (121 / 399879)) (n := 12)
    (lo := (605183 / 1000000000)) (hi := (1182 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199879) = 1/(199879 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13031 : Bounds (-1182 / 1953125) (-605183 / 1000000000) (Real.log (199879 / 200000)) := by
  have h := reflection_log_13031_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13032_neg : (279819493 / 1000000000) ≤ -Real.log (1000000 / 1322891) ∧
    -Real.log (1000000 / 1322891) ≤ (139909747 / 500000000) := by
  have h := checkLog_sound (w := (322891 / 2322891)) (n := 12)
    (lo := (279819493 / 1000000000)) (hi := (139909747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1322891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1322891 / 1000000) = 1/(1000000 / 1322891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13032 : Bounds (279819493 / 1000000000) (139909747 / 500000000) (Real.log (1322891 / 1000000)) := by
  have h := reflection_log_13032_neg
  have he : Real.log (1322891 / 1000000) = -Real.log (1000000 / 1322891) := by
    rw [show ((1322891 / 1000000) : ℝ) = ((1000000 / 1322891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13033_neg : (194961507 / 500000000) ≤ -Real.log (677109 / 1000000) ∧
    -Real.log (677109 / 1000000) ≤ (77984603 / 200000000) := by
  have h := checkLog_sound (w := (322891 / 1677109)) (n := 12)
    (lo := (194961507 / 500000000)) (hi := (77984603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 677109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 677109) = 1/(677109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13033 : Bounds (-77984603 / 200000000) (-194961507 / 500000000) (Real.log (677109 / 1000000)) := by
  have h := reflection_log_13033_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13034_neg : (281645639 / 1000000000) ≤ -Real.log (1000000 / 1325309) ∧
    -Real.log (1000000 / 1325309) ≤ (7041141 / 25000000) := by
  have h := checkLog_sound (w := (325309 / 2325309)) (n := 12)
    (lo := (281645639 / 1000000000)) (hi := (7041141 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325309 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325309 / 1000000) = 1/(1000000 / 1325309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13034 : Bounds (281645639 / 1000000000) (7041141 / 25000000) (Real.log (1325309 / 1000000)) := by
  have h := reflection_log_13034_neg
  have he : Real.log (1325309 / 1000000) = -Real.log (1000000 / 1325309) := by
    rw [show ((1325309 / 1000000) : ℝ) = ((1000000 / 1325309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13035_neg : (39350047 / 100000000) ≤ -Real.log (674691 / 1000000) ∧
    -Real.log (674691 / 1000000) ≤ (393500471 / 1000000000) := by
  have h := checkLog_sound (w := (325309 / 1674691)) (n := 12)
    (lo := (39350047 / 100000000)) (hi := (393500471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 674691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 674691) = 1/(674691 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13035 : Bounds (-393500471 / 1000000000) (-39350047 / 100000000) (Real.log (674691 / 1000000)) := by
  have h := reflection_log_13035_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13036_neg : (11185483 / 100000000) ≤ -Real.log (894174054519 / 1000000000000) ∧
    -Real.log (894174054519 / 1000000000000) ≤ (111854831 / 1000000000) := by
  have h := checkLog_sound (w := (105825945481 / 1894174054519)) (n := 12)
    (lo := (11185483 / 100000000)) (hi := (111854831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 894174054519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 894174054519) = 1/(894174054519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13036 : Bounds (-111854831 / 1000000000) (-11185483 / 100000000) (Real.log (894174054519 / 1000000000000)) := by
  have h := reflection_log_13036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13037_neg : (110103521 / 1000000000) ≤ -Real.log (895741402119 / 1000000000000) ∧
    -Real.log (895741402119 / 1000000000000) ≤ (55051761 / 500000000) := by
  have h := checkLog_sound (w := (104258597881 / 1895741402119)) (n := 12)
    (lo := (110103521 / 1000000000)) (hi := (55051761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 895741402119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 895741402119) = 1/(895741402119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13037 : Bounds (-55051761 / 500000000) (-110103521 / 1000000000) (Real.log (895741402119 / 1000000000000)) := by
  have h := reflection_log_13037_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13038_neg : (669742507 / 1000000000) ≤ -Real.log (500000000000 / 976867092299) ∧
    -Real.log (500000000000 / 976867092299) ≤ (167435627 / 250000000) := by
  have h := checkLog_sound (w := (476867092299 / 1476867092299)) (n := 12)
    (lo := (669742507 / 1000000000)) (hi := (167435627 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976867092299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976867092299 / 500000000000) = 1/(500000000000 / 976867092299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13038 : Bounds (669742507 / 1000000000) (167435627 / 250000000) (Real.log (976867092299 / 500000000000)) := by
  have h := reflection_log_13038_neg
  have he : Real.log (976867092299 / 500000000000) = -Real.log (500000000000 / 976867092299) := by
    rw [show ((976867092299 / 500000000000) : ℝ) = ((500000000000 / 976867092299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13039_neg : (67514611 / 100000000) ≤ -Real.log (100000000000 / 196431996277) ∧
    -Real.log (100000000000 / 196431996277) ≤ (675146111 / 1000000000) := by
  have h := checkLog_sound (w := (96431996277 / 296431996277)) (n := 12)
    (lo := (67514611 / 100000000)) (hi := (675146111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196431996277 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196431996277 / 100000000000) = 1/(100000000000 / 196431996277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13039 : Bounds (67514611 / 100000000) (675146111 / 1000000000) (Real.log (196431996277 / 100000000000)) := by
  have h := reflection_log_13039_neg
  have he : Real.log (196431996277 / 100000000000) = -Real.log (100000000000 / 196431996277) := by
    rw [show ((196431996277 / 100000000000) : ℝ) = ((100000000000 / 196431996277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13040_neg : (1392556121 / 1000000000) ≤ -Real.log (50000000000 / 201256281407) ∧
    -Real.log (50000000000 / 201256281407) ≤ (348139031 / 250000000) := by
  have h := checkLog_sound (w := (1256281407 / 401256281407)) (n := 12)
    (lo := (6261761 / 1000000000)) (hi := (3130881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201256281407 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(201256281407 / 200000000000) = 1/(50000000000 / 201256281407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13040 : Bounds (1392556121 / 1000000000) (348139031 / 250000000) (Real.log (201256281407 / 50000000000)) := by
  have h := reflection_log_13040_neg
  have he : Real.log (201256281407 / 50000000000) = -Real.log (50000000000 / 201256281407) := by
    rw [show ((201256281407 / 50000000000) : ℝ) = ((50000000000 / 201256281407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13041_neg : (1401993269 / 1000000000) ≤ -Real.log (500000000000 / 2031645569621) ∧
    -Real.log (500000000000 / 2031645569621) ≤ (175249159 / 125000000) := by
  have h := checkLog_sound (w := (31645569621 / 4031645569621)) (n := 12)
    (lo := (15698909 / 1000000000)) (hi := (1569891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2031645569621 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2031645569621 / 2000000000000) = 1/(500000000000 / 2031645569621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13041 : Bounds (1401993269 / 1000000000) (175249159 / 125000000) (Real.log (2031645569621 / 500000000000)) := by
  have h := reflection_log_13041_neg
  have he : Real.log (2031645569621 / 500000000000) = -Real.log (500000000000 / 2031645569621) := by
    rw [show ((2031645569621 / 500000000000) : ℝ) = ((500000000000 / 2031645569621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13042_neg : (47499117 / 100000000) ≤ -Real.log (125 / 201) ∧
    -Real.log (125 / 201) ≤ (474991171 / 1000000000) := by
  have h := checkLog_sound (w := (38 / 163)) (n := 12)
    (lo := (47499117 / 100000000)) (hi := (474991171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201 / 125) = 1/(125 / 201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13042 : Bounds (47499117 / 100000000) (474991171 / 1000000000) (Real.log (201 / 125)) := by
  have h := reflection_log_13042_neg
  have he : Real.log (201 / 125) = -Real.log (125 / 201) := by
    rw [show ((201 / 125) : ℝ) = ((125 / 201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13043_neg : (468246719 / 500000000) ≤ -Real.log (49 / 125) ∧
    -Real.log (49 / 125) ≤ (1463271 / 1562500) := by
  have h := checkLog_sound (w := (27 / 223)) (n := 12)
    (lo := (121673129 / 500000000)) (hi := (243346259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 98) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 98) = 1/(49 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13043 : Bounds (-1463271 / 1562500) (-468246719 / 500000000) (Real.log (49 / 125)) := by
  have h := reflection_log_13043_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13044_neg : (121563 / 200000000) ≤ -Real.log (31250 / 31269) ∧
    -Real.log (31250 / 31269) ≤ (75977 / 125000000) := by
  have h := checkLog_sound (w := (19 / 62519)) (n := 12)
    (lo := (121563 / 200000000)) (hi := (75977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31269 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31269 / 31250) = 1/(31250 / 31269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13044 : Bounds (121563 / 200000000) (75977 / 125000000) (Real.log (31269 / 31250)) := by
  have h := reflection_log_13044_neg
  have he : Real.log (31269 / 31250) = -Real.log (31250 / 31269) := by
    rw [show ((31269 / 31250) : ℝ) = ((31250 / 31269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13045_neg : (76023 / 125000000) ≤ -Real.log (31231 / 31250) ∧
    -Real.log (31231 / 31250) ≤ (121637 / 200000000) := by
  have h := checkLog_sound (w := (19 / 62481)) (n := 12)
    (lo := (76023 / 125000000)) (hi := (121637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 31231) = 1/(31231 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13045 : Bounds (-121637 / 200000000) (-76023 / 125000000) (Real.log (31231 / 31250)) := by
  have h := reflection_log_13045_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13046_neg : (140613013 / 500000000) ≤ -Real.log (1000000 / 1324753) ∧
    -Real.log (1000000 / 1324753) ≤ (281226027 / 1000000000) := by
  have h := checkLog_sound (w := (324753 / 2324753)) (n := 12)
    (lo := (140613013 / 500000000)) (hi := (281226027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1324753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1324753 / 1000000) = 1/(1000000 / 1324753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13046 : Bounds (140613013 / 500000000) (281226027 / 1000000000) (Real.log (1324753 / 1000000)) := by
  have h := reflection_log_13046_neg
  have he : Real.log (1324753 / 1000000) = -Real.log (1000000 / 1324753) := by
    rw [show ((1324753 / 1000000) : ℝ) = ((1000000 / 1324753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13047_neg : (392676729 / 1000000000) ≤ -Real.log (675247 / 1000000) ∧
    -Real.log (675247 / 1000000) ≤ (39267673 / 100000000) := by
  have h := checkLog_sound (w := (324753 / 1675247)) (n := 12)
    (lo := (392676729 / 1000000000)) (hi := (39267673 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 675247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 675247) = 1/(675247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13047 : Bounds (-39267673 / 100000000) (-392676729 / 1000000000) (Real.log (675247 / 1000000)) := by
  have h := reflection_log_13047_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13048_neg : (70763909 / 250000000) ≤ -Real.log (1000000 / 1327179) ∧
    -Real.log (1000000 / 1327179) ≤ (283055637 / 1000000000) := by
  have h := checkLog_sound (w := (327179 / 2327179)) (n := 12)
    (lo := (70763909 / 250000000)) (hi := (283055637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327179 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1327179 / 1000000) = 1/(1000000 / 1327179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13048 : Bounds (70763909 / 250000000) (283055637 / 1000000000) (Real.log (1327179 / 1000000)) := by
  have h := reflection_log_13048_neg
  have he : Real.log (1327179 / 1000000) = -Real.log (1000000 / 1327179) := by
    rw [show ((1327179 / 1000000) : ℝ) = ((1000000 / 1327179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13049_neg : (396275957 / 1000000000) ≤ -Real.log (672821 / 1000000) ∧
    -Real.log (672821 / 1000000) ≤ (198137979 / 500000000) := by
  have h := checkLog_sound (w := (327179 / 1672821)) (n := 12)
    (lo := (396275957 / 1000000000)) (hi := (198137979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 672821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 672821) = 1/(672821 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13049 : Bounds (-198137979 / 500000000) (-396275957 / 1000000000) (Real.log (672821 / 1000000)) := by
  have h := reflection_log_13049_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13050_neg : (707627 / 6250000) ≤ -Real.log (892953901959 / 1000000000000) ∧
    -Real.log (892953901959 / 1000000000000) ≤ (113220321 / 1000000000) := by
  have h := checkLog_sound (w := (107046098041 / 1892953901959)) (n := 12)
    (lo := (707627 / 6250000)) (hi := (113220321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 892953901959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 892953901959) = 1/(892953901959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13050 : Bounds (-113220321 / 1000000000) (-707627 / 6250000) (Real.log (892953901959 / 1000000000000)) := by
  have h := reflection_log_13050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13051_neg : (55725351 / 500000000) ≤ -Real.log (894535488991 / 1000000000000) ∧
    -Real.log (894535488991 / 1000000000000) ≤ (111450703 / 1000000000) := by
  have h := checkLog_sound (w := (105464511009 / 1894535488991)) (n := 12)
    (lo := (55725351 / 500000000)) (hi := (111450703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 894535488991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 894535488991) = 1/(894535488991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13051 : Bounds (-111450703 / 1000000000) (-55725351 / 500000000) (Real.log (894535488991 / 1000000000000)) := by
  have h := reflection_log_13051_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13052_neg : (168475689 / 250000000) ≤ -Real.log (500000000000 / 980939567299) ∧
    -Real.log (500000000000 / 980939567299) ≤ (673902757 / 1000000000) := by
  have h := checkLog_sound (w := (480939567299 / 1480939567299)) (n := 12)
    (lo := (168475689 / 250000000)) (hi := (673902757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980939567299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980939567299 / 500000000000) = 1/(500000000000 / 980939567299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13052 : Bounds (168475689 / 250000000) (673902757 / 1000000000) (Real.log (980939567299 / 500000000000)) := by
  have h := reflection_log_13052_neg
  have he : Real.log (980939567299 / 500000000000) = -Real.log (500000000000 / 980939567299) := by
    rw [show ((980939567299 / 500000000000) : ℝ) = ((500000000000 / 980939567299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13053_neg : (339665797 / 500000000) ≤ -Real.log (125000000000 / 246569852903) ∧
    -Real.log (125000000000 / 246569852903) ≤ (135866319 / 200000000) := by
  have h := checkLog_sound (w := (121569852903 / 371569852903)) (n := 12)
    (lo := (339665797 / 500000000)) (hi := (135866319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246569852903 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246569852903 / 125000000000) = 1/(125000000000 / 246569852903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13053 : Bounds (339665797 / 500000000) (135866319 / 200000000) (Real.log (246569852903 / 125000000000)) := by
  have h := reflection_log_13053_neg
  have he : Real.log (246569852903 / 125000000000) = -Real.log (125000000000 / 246569852903) := by
    rw [show ((246569852903 / 125000000000) : ℝ) = ((125000000000 / 246569852903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13054_neg : (1401993269 / 1000000000) ≤ -Real.log (25000000000 / 101582278481) ∧
    -Real.log (25000000000 / 101582278481) ≤ (175249159 / 125000000) := by
  have h := checkLog_sound (w := (1582278481 / 201582278481)) (n := 12)
    (lo := (15698909 / 1000000000)) (hi := (1569891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101582278481 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(101582278481 / 100000000000) = 1/(25000000000 / 101582278481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13054 : Bounds (1401993269 / 1000000000) (175249159 / 125000000) (Real.log (101582278481 / 25000000000)) := by
  have h := reflection_log_13054_neg
  have he : Real.log (101582278481 / 25000000000) = -Real.log (25000000000 / 101582278481) := by
    rw [show ((101582278481 / 25000000000) : ℝ) = ((25000000000 / 101582278481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13055_neg : (22054447 / 15625000) ≤ -Real.log (125000000000 / 512755102041) ∧
    -Real.log (125000000000 / 512755102041) ≤ (1411484611 / 1000000000) := by
  have h := checkLog_sound (w := (12755102041 / 1012755102041)) (n := 12)
    (lo := (3148781 / 125000000)) (hi := (25190249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512755102041 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(512755102041 / 500000000000) = 1/(125000000000 / 512755102041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13055 : Bounds (22054447 / 15625000) (1411484611 / 1000000000) (Real.log (512755102041 / 125000000000)) := by
  have h := reflection_log_13055_neg
  have he : Real.log (512755102041 / 125000000000) = -Real.log (125000000000 / 512755102041) := by
    rw [show ((512755102041 / 125000000000) : ℝ) = ((125000000000 / 512755102041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11968_neg : (9599 / 15625) ≤ -Real.log (541 / 1000) ∧
    -Real.log (541 / 1000) ≤ (614336001 / 1000000000) := by
  have h := checkLog_sound (w := (459 / 1541)) (n := 12)
    (lo := (9599 / 15625)) (hi := (614336001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 541) = 1/(541 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11968 : Bounds (-614336001 / 1000000000) (-9599 / 15625) (Real.log (541 / 1000)) := by
  have h := reflection_log_11968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11969_neg : (229447 / 500000000) ≤ -Real.log (1000000 / 1000459) ∧
    -Real.log (1000000 / 1000459) ≤ (91779 / 200000000) := by
  have h := checkLog_sound (w := (459 / 2000459)) (n := 12)
    (lo := (229447 / 500000000)) (hi := (91779 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000459 / 1000000) = 1/(1000000 / 1000459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11969 : Bounds (229447 / 500000000) (91779 / 200000000) (Real.log (1000459 / 1000000)) := by
  have h := reflection_log_11969_neg
  have he : Real.log (1000459 / 1000000) = -Real.log (1000000 / 1000459) := by
    rw [show ((1000459 / 1000000) : ℝ) = ((1000000 / 1000459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11970_neg : (91821 / 200000000) ≤ -Real.log (999541 / 1000000) ∧
    -Real.log (999541 / 1000000) ≤ (229553 / 500000000) := by
  have h := checkLog_sound (w := (459 / 1999541)) (n := 12)
    (lo := (91821 / 200000000)) (hi := (229553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999541) = 1/(999541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11970 : Bounds (-229553 / 500000000) (-91821 / 200000000) (Real.log (999541 / 1000000)) := by
  have h := reflection_log_11970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11971_neg : (213519791 / 1000000000) ≤ -Real.log (250000 / 309507) ∧
    -Real.log (250000 / 309507) ≤ (13344987 / 62500000) := by
  have h := checkLog_sound (w := (59507 / 559507)) (n := 12)
    (lo := (213519791 / 1000000000)) (hi := (13344987 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309507 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309507 / 250000) = 1/(250000 / 309507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11971 : Bounds (213519791 / 1000000000) (13344987 / 62500000) (Real.log (309507 / 250000)) := by
  have h := reflection_log_11971_neg
  have he : Real.log (309507 / 250000) = -Real.log (250000 / 309507) := by
    rw [show ((309507 / 250000) : ℝ) = ((250000 / 309507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11972_neg : (271845469 / 1000000000) ≤ -Real.log (190493 / 250000) ∧
    -Real.log (190493 / 250000) ≤ (27184547 / 100000000) := by
  have h := checkLog_sound (w := (59507 / 440493)) (n := 12)
    (lo := (271845469 / 1000000000)) (hi := (27184547 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 190493) = 1/(190493 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11972 : Bounds (-27184547 / 100000000) (-271845469 / 1000000000) (Real.log (190493 / 250000)) := by
  have h := reflection_log_11972_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11973_neg : (107164811 / 500000000) ≤ -Real.log (1000000 / 1239031) ∧
    -Real.log (1000000 / 1239031) ≤ (214329623 / 1000000000) := by
  have h := checkLog_sound (w := (239031 / 2239031)) (n := 12)
    (lo := (107164811 / 500000000)) (hi := (214329623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239031 / 1000000) = 1/(1000000 / 1239031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11973 : Bounds (107164811 / 500000000) (214329623 / 1000000000) (Real.log (1239031 / 1000000)) := by
  have h := reflection_log_11973_neg
  have he : Real.log (1239031 / 1000000) = -Real.log (1000000 / 1239031) := by
    rw [show ((1239031 / 1000000) : ℝ) = ((1000000 / 1239031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11974_neg : (273162657 / 1000000000) ≤ -Real.log (760969 / 1000000) ∧
    -Real.log (760969 / 1000000) ≤ (136581329 / 500000000) := by
  have h := checkLog_sound (w := (239031 / 1760969)) (n := 12)
    (lo := (273162657 / 1000000000)) (hi := (136581329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760969) = 1/(760969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11974 : Bounds (-136581329 / 500000000) (-273162657 / 1000000000) (Real.log (760969 / 1000000)) := by
  have h := reflection_log_11974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11975_neg : (11766607 / 200000000) ≤ -Real.log (942864181039 / 1000000000000) ∧
    -Real.log (942864181039 / 1000000000000) ≤ (14708259 / 250000000) := by
  have h := checkLog_sound (w := (57135818961 / 1942864181039)) (n := 12)
    (lo := (11766607 / 200000000)) (hi := (14708259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 942864181039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 942864181039) = 1/(942864181039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11975 : Bounds (-14708259 / 250000000) (-11766607 / 200000000) (Real.log (942864181039 / 1000000000000)) := by
  have h := reflection_log_11975_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11976_neg : (29162839 / 500000000) ≤ -Real.log (58958916951 / 62500000000) ∧
    -Real.log (58958916951 / 62500000000) ≤ (58325679 / 1000000000) := by
  have h := checkLog_sound (w := (3541083049 / 121458916951)) (n := 12)
    (lo := (29162839 / 500000000)) (hi := (58325679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58958916951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58958916951) = 1/(58958916951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11976 : Bounds (-58325679 / 1000000000) (-29162839 / 500000000) (Real.log (58958916951 / 62500000000)) := by
  have h := reflection_log_11976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11977_neg : (24268263 / 50000000) ≤ -Real.log (100000000000 / 162476836419) ∧
    -Real.log (100000000000 / 162476836419) ≤ (485365261 / 1000000000) := by
  have h := checkLog_sound (w := (62476836419 / 262476836419)) (n := 12)
    (lo := (24268263 / 50000000)) (hi := (485365261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162476836419 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162476836419 / 100000000000) = 1/(100000000000 / 162476836419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11977 : Bounds (24268263 / 50000000) (485365261 / 1000000000) (Real.log (162476836419 / 100000000000)) := by
  have h := reflection_log_11977_neg
  have he : Real.log (162476836419 / 100000000000) = -Real.log (100000000000 / 162476836419) := by
    rw [show ((162476836419 / 100000000000) : ℝ) = ((100000000000 / 162476836419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11978_neg : (12187307 / 25000000) ≤ -Real.log (250000000000 / 407056989181) ∧
    -Real.log (250000000000 / 407056989181) ≤ (487492281 / 1000000000) := by
  have h := checkLog_sound (w := (157056989181 / 657056989181)) (n := 12)
    (lo := (12187307 / 25000000)) (hi := (487492281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407056989181 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407056989181 / 250000000000) = 1/(250000000000 / 407056989181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11978 : Bounds (12187307 / 25000000) (487492281 / 1000000000) (Real.log (407056989181 / 250000000000)) := by
  have h := reflection_log_11978_neg
  have he : Real.log (407056989181 / 250000000000) = -Real.log (250000000000 / 407056989181) := by
    rw [show ((407056989181 / 250000000000) : ℝ) = ((250000000000 / 407056989181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11979_neg : (98955491 / 100000000) ≤ -Real.log (62500000000 / 168127306273) ∧
    -Real.log (62500000000 / 168127306273) ≤ (30923591 / 31250000) := by
  have h := checkLog_sound (w := (43127306273 / 293127306273)) (n := 12)
    (lo := (29640773 / 100000000)) (hi := (296407731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168127306273 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(168127306273 / 125000000000) = 1/(62500000000 / 168127306273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11979 : Bounds (98955491 / 100000000) (30923591 / 31250000) (Real.log (168127306273 / 62500000000)) := by
  have h := reflection_log_11979_neg
  have he : Real.log (168127306273 / 62500000000) = -Real.log (62500000000 / 168127306273) := by
    rw [show ((168127306273 / 62500000000) : ℝ) = ((62500000000 / 168127306273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11980_neg : (992087269 / 1000000000) ≤ -Real.log (50000000000 / 134842883549) ∧
    -Real.log (50000000000 / 134842883549) ≤ (992087271 / 1000000000) := by
  have h := checkLog_sound (w := (34842883549 / 234842883549)) (n := 12)
    (lo := (298940089 / 1000000000)) (hi := (29894009 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134842883549 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(134842883549 / 100000000000) = 1/(50000000000 / 134842883549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11980 : Bounds (992087269 / 1000000000) (992087271 / 1000000000) (Real.log (134842883549 / 50000000000)) := by
  have h := reflection_log_11980_neg
  have he : Real.log (134842883549 / 50000000000) = -Real.log (50000000000 / 134842883549) := by
    rw [show ((134842883549 / 50000000000) : ℝ) = ((50000000000 / 134842883549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11981_neg : (75687287 / 200000000) ≤ -Real.log (50 / 73) ∧
    -Real.log (50 / 73) ≤ (94609109 / 250000000) := by
  have h := checkLog_sound (w := (23 / 123)) (n := 12)
    (lo := (75687287 / 200000000)) (hi := (94609109 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73 / 50) = 1/(50 / 73) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11981 : Bounds (75687287 / 200000000) (94609109 / 250000000) (Real.log (73 / 50)) := by
  have h := reflection_log_11981_neg
  have he : Real.log (73 / 50) = -Real.log (50 / 73) := by
    rw [show ((73 / 50) : ℝ) = ((50 / 73) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11982_neg : (616186139 / 1000000000) ≤ -Real.log (27 / 50) ∧
    -Real.log (27 / 50) ≤ (30809307 / 50000000) := by
  have h := checkLog_sound (w := (23 / 77)) (n := 12)
    (lo := (616186139 / 1000000000)) (hi := (30809307 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 27) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 27) = 1/(27 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11982 : Bounds (-30809307 / 50000000) (-616186139 / 1000000000) (Real.log (27 / 50)) := by
  have h := reflection_log_11982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11983_neg : (229947 / 500000000) ≤ -Real.log (50000 / 50023) ∧
    -Real.log (50000 / 50023) ≤ (91979 / 200000000) := by
  have h := checkLog_sound (w := (23 / 100023)) (n := 12)
    (lo := (229947 / 500000000)) (hi := (91979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50023 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50023 / 50000) = 1/(50000 / 50023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11983 : Bounds (229947 / 500000000) (91979 / 200000000) (Real.log (50023 / 50000)) := by
  have h := reflection_log_11983_neg
  have he : Real.log (50023 / 50000) = -Real.log (50000 / 50023) := by
    rw [show ((50023 / 50000) : ℝ) = ((50000 / 50023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11984_neg : (92021 / 200000000) ≤ -Real.log (49977 / 50000) ∧
    -Real.log (49977 / 50000) ≤ (230053 / 500000000) := by
  have h := checkLog_sound (w := (23 / 99977)) (n := 12)
    (lo := (92021 / 200000000)) (hi := (230053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49977) = 1/(49977 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11984 : Bounds (-230053 / 500000000) (-92021 / 200000000) (Real.log (49977 / 50000)) := by
  have h := reflection_log_11984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11985_neg : (213974443 / 1000000000) ≤ -Real.log (1000000 / 1238591) ∧
    -Real.log (1000000 / 1238591) ≤ (53493611 / 250000000) := by
  have h := checkLog_sound (w := (238591 / 2238591)) (n := 12)
    (lo := (213974443 / 1000000000)) (hi := (53493611 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238591 / 1000000) = 1/(1000000 / 1238591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11985 : Bounds (213974443 / 1000000000) (53493611 / 250000000) (Real.log (1238591 / 1000000)) := by
  have h := reflection_log_11985_neg
  have he : Real.log (1238591 / 1000000) = -Real.log (1000000 / 1238591) := by
    rw [show ((1238591 / 1000000) : ℝ) = ((1000000 / 1238591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11986_neg : (136292307 / 500000000) ≤ -Real.log (761409 / 1000000) ∧
    -Real.log (761409 / 1000000) ≤ (54516923 / 200000000) := by
  have h := checkLog_sound (w := (238591 / 1761409)) (n := 12)
    (lo := (136292307 / 500000000)) (hi := (54516923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761409) = 1/(761409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11986 : Bounds (-54516923 / 200000000) (-136292307 / 500000000) (Real.log (761409 / 1000000)) := by
  have h := reflection_log_11986_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11987_neg : (2684819 / 12500000) ≤ -Real.log (250000 / 309899) ∧
    -Real.log (250000 / 309899) ≤ (214785521 / 1000000000) := by
  have h := checkLog_sound (w := (59899 / 559899)) (n := 12)
    (lo := (2684819 / 12500000)) (hi := (214785521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309899 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309899 / 250000) = 1/(250000 / 309899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11987 : Bounds (2684819 / 12500000) (214785521 / 1000000000) (Real.log (309899 / 250000)) := by
  have h := reflection_log_11987_neg
  have he : Real.log (309899 / 250000) = -Real.log (250000 / 309899) := by
    rw [show ((309899 / 250000) : ℝ) = ((250000 / 309899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11988_neg : (273905407 / 1000000000) ≤ -Real.log (190101 / 250000) ∧
    -Real.log (190101 / 250000) ≤ (1069943 / 3906250) := by
  have h := checkLog_sound (w := (59899 / 440101)) (n := 12)
    (lo := (273905407 / 1000000000)) (hi := (1069943 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 190101) = 1/(190101 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11988 : Bounds (-1069943 / 3906250) (-273905407 / 1000000000) (Real.log (190101 / 250000)) := by
  have h := reflection_log_11988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11989_neg : (59119887 / 1000000000) ≤ -Real.log (58912109799 / 62500000000) ∧
    -Real.log (58912109799 / 62500000000) ≤ (3694993 / 62500000) := by
  have h := checkLog_sound (w := (3587890201 / 121412109799)) (n := 12)
    (lo := (59119887 / 1000000000)) (hi := (3694993 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58912109799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58912109799) = 1/(58912109799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11989 : Bounds (-3694993 / 62500000) (-59119887 / 1000000000) (Real.log (58912109799 / 62500000000)) := by
  have h := reflection_log_11989_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11990_neg : (58610171 / 1000000000) ≤ -Real.log (943074334719 / 1000000000000) ∧
    -Real.log (943074334719 / 1000000000000) ≤ (14652543 / 250000000) := by
  have h := checkLog_sound (w := (56925665281 / 1943074334719)) (n := 12)
    (lo := (58610171 / 1000000000)) (hi := (14652543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 943074334719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 943074334719) = 1/(943074334719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11990 : Bounds (-14652543 / 250000000) (-58610171 / 1000000000) (Real.log (943074334719 / 1000000000000)) := by
  have h := reflection_log_11990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11991_neg : (486559057 / 1000000000) ≤ -Real.log (50000000000 / 81335458341) ∧
    -Real.log (50000000000 / 81335458341) ≤ (243279529 / 500000000) := by
  have h := checkLog_sound (w := (31335458341 / 131335458341)) (n := 12)
    (lo := (486559057 / 1000000000)) (hi := (243279529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81335458341 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81335458341 / 50000000000) = 1/(50000000000 / 81335458341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11991 : Bounds (486559057 / 1000000000) (243279529 / 500000000) (Real.log (81335458341 / 50000000000)) := by
  have h := reflection_log_11991_neg
  have he : Real.log (81335458341 / 50000000000) = -Real.log (50000000000 / 81335458341) := by
    rw [show ((81335458341 / 50000000000) : ℝ) = ((50000000000 / 81335458341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11992_neg : (30543183 / 62500000) ≤ -Real.log (100000000000 / 163018079863) ∧
    -Real.log (100000000000 / 163018079863) ≤ (488690929 / 1000000000) := by
  have h := checkLog_sound (w := (63018079863 / 263018079863)) (n := 12)
    (lo := (30543183 / 62500000)) (hi := (488690929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163018079863 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163018079863 / 100000000000) = 1/(100000000000 / 163018079863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11992 : Bounds (30543183 / 62500000) (488690929 / 1000000000) (Real.log (163018079863 / 100000000000)) := by
  have h := reflection_log_11992_neg
  have he : Real.log (163018079863 / 100000000000) = -Real.log (100000000000 / 163018079863) := by
    rw [show ((163018079863 / 100000000000) : ℝ) = ((100000000000 / 163018079863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11993_neg : (992087269 / 1000000000) ≤ -Real.log (500000000000 / 1348428835489) ∧
    -Real.log (500000000000 / 1348428835489) ≤ (992087271 / 1000000000) := by
  have h := checkLog_sound (w := (348428835489 / 2348428835489)) (n := 12)
    (lo := (298940089 / 1000000000)) (hi := (29894009 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348428835489 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1348428835489 / 1000000000000) = 1/(500000000000 / 1348428835489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11993 : Bounds (992087269 / 1000000000) (992087271 / 1000000000) (Real.log (1348428835489 / 500000000000)) := by
  have h := reflection_log_11993_neg
  have he : Real.log (1348428835489 / 500000000000) = -Real.log (500000000000 / 1348428835489) := by
    rw [show ((1348428835489 / 500000000000) : ℝ) = ((500000000000 / 1348428835489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11994_neg : (497311287 / 500000000) ≤ -Real.log (125000000000 / 337962962963) ∧
    -Real.log (125000000000 / 337962962963) ≤ (62163911 / 62500000) := by
  have h := checkLog_sound (w := (87962962963 / 587962962963)) (n := 12)
    (lo := (150737697 / 500000000)) (hi := (60295079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337962962963 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(337962962963 / 250000000000) = 1/(125000000000 / 337962962963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11994 : Bounds (497311287 / 500000000) (62163911 / 62500000) (Real.log (337962962963 / 125000000000)) := by
  have h := reflection_log_11994_neg
  have he : Real.log (337962962963 / 125000000000) = -Real.log (125000000000 / 337962962963) := by
    rw [show ((337962962963 / 125000000000) : ℝ) = ((125000000000 / 337962962963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11995_neg : (94780283 / 250000000) ≤ -Real.log (1000 / 1461) ∧
    -Real.log (1000 / 1461) ≤ (379121133 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 2461)) (n := 12)
    (lo := (94780283 / 250000000)) (hi := (379121133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1461 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1461 / 1000) = 1/(1000 / 1461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11995 : Bounds (94780283 / 250000000) (379121133 / 1000000000) (Real.log (1461 / 1000)) := by
  have h := reflection_log_11995_neg
  have he : Real.log (1461 / 1000) = -Real.log (1000 / 1461) := by
    rw [show ((1461 / 1000) : ℝ) = ((1000 / 1461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11996_neg : (154509927 / 250000000) ≤ -Real.log (539 / 1000) ∧
    -Real.log (539 / 1000) ≤ (618039709 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 1539)) (n := 12)
    (lo := (154509927 / 250000000)) (hi := (618039709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 539) = 1/(539 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11996 : Bounds (-618039709 / 1000000000) (-154509927 / 250000000) (Real.log (539 / 1000)) := by
  have h := reflection_log_11996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11997_neg : (460893 / 1000000000) ≤ -Real.log (1000000 / 1000461) ∧
    -Real.log (1000000 / 1000461) ≤ (230447 / 500000000) := by
  have h := checkLog_sound (w := (461 / 2000461)) (n := 12)
    (lo := (460893 / 1000000000)) (hi := (230447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000461 / 1000000) = 1/(1000000 / 1000461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11997 : Bounds (460893 / 1000000000) (230447 / 500000000) (Real.log (1000461 / 1000000)) := by
  have h := reflection_log_11997_neg
  have he : Real.log (1000461 / 1000000) = -Real.log (1000000 / 1000461) := by
    rw [show ((1000461 / 1000000) : ℝ) = ((1000000 / 1000461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11998_neg : (230553 / 500000000) ≤ -Real.log (999539 / 1000000) ∧
    -Real.log (999539 / 1000000) ≤ (461107 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 1999539)) (n := 12)
    (lo := (230553 / 500000000)) (hi := (461107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999539) = 1/(999539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11998 : Bounds (-461107 / 1000000000) (-230553 / 500000000) (Real.log (999539 / 1000000)) := by
  have h := reflection_log_11998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11999_neg : (42885939 / 200000000) ≤ -Real.log (200000 / 247831) ∧
    -Real.log (200000 / 247831) ≤ (418808 / 1953125) := by
  have h := checkLog_sound (w := (47831 / 447831)) (n := 12)
    (lo := (42885939 / 200000000)) (hi := (418808 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247831 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247831 / 200000) = 1/(200000 / 247831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11999 : Bounds (42885939 / 200000000) (418808 / 1953125) (Real.log (247831 / 200000)) := by
  have h := reflection_log_11999_neg
  have he : Real.log (247831 / 200000) = -Real.log (200000 / 247831) := by
    rw [show ((247831 / 200000) : ℝ) = ((200000 / 247831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12000_neg : (273325621 / 1000000000) ≤ -Real.log (152169 / 200000) ∧
    -Real.log (152169 / 200000) ≤ (136662811 / 500000000) := by
  have h := checkLog_sound (w := (47831 / 352169)) (n := 12)
    (lo := (273325621 / 1000000000)) (hi := (136662811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152169) = 1/(152169 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12000 : Bounds (-136662811 / 500000000) (-273325621 / 1000000000) (Real.log (152169 / 200000)) := by
  have h := reflection_log_12000_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12001_neg : (215240403 / 1000000000) ≤ -Real.log (6250 / 7751) ∧
    -Real.log (6250 / 7751) ≤ (53810101 / 250000000) := by
  have h := checkLog_sound (w := (1501 / 14001)) (n := 12)
    (lo := (215240403 / 1000000000)) (hi := (53810101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7751 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7751 / 6250) = 1/(6250 / 7751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12001 : Bounds (215240403 / 1000000000) (53810101 / 250000000) (Real.log (7751 / 6250)) := by
  have h := reflection_log_12001_neg
  have he : Real.log (7751 / 6250) = -Real.log (6250 / 7751) := by
    rw [show ((7751 / 6250) : ℝ) = ((6250 / 7751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12002_neg : (137323697 / 500000000) ≤ -Real.log (4749 / 6250) ∧
    -Real.log (4749 / 6250) ≤ (54929479 / 200000000) := by
  have h := checkLog_sound (w := (1501 / 10999)) (n := 12)
    (lo := (137323697 / 500000000)) (hi := (54929479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 4749) = 1/(4749 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12002 : Bounds (-54929479 / 200000000) (-137323697 / 500000000) (Real.log (4749 / 6250)) := by
  have h := reflection_log_12002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12003_neg : (5940699 / 100000000) ≤ -Real.log (36809499 / 39062500) ∧
    -Real.log (36809499 / 39062500) ≤ (59406991 / 1000000000) := by
  have h := checkLog_sound (w := (2253001 / 75871999)) (n := 12)
    (lo := (5940699 / 100000000)) (hi := (59406991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 36809499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 36809499) = 1/(36809499 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12003 : Bounds (-59406991 / 1000000000) (-5940699 / 100000000) (Real.log (36809499 / 39062500)) := by
  have h := reflection_log_12003_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12004_neg : (2355837 / 40000000) ≤ -Real.log (37712195439 / 40000000000) ∧
    -Real.log (37712195439 / 40000000000) ≤ (29447963 / 500000000) := by
  have h := checkLog_sound (w := (2287804561 / 77712195439)) (n := 12)
    (lo := (2355837 / 40000000)) (hi := (29447963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37712195439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37712195439) = 1/(37712195439 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12004 : Bounds (-29447963 / 500000000) (-2355837 / 40000000) (Real.log (37712195439 / 40000000000)) := by
  have h := reflection_log_12004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12005_neg : (121938829 / 250000000) ≤ -Real.log (125000000000 / 203582037077) ∧
    -Real.log (125000000000 / 203582037077) ≤ (487755317 / 1000000000) := by
  have h := checkLog_sound (w := (78582037077 / 328582037077)) (n := 12)
    (lo := (121938829 / 250000000)) (hi := (487755317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203582037077 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203582037077 / 125000000000) = 1/(125000000000 / 203582037077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12005 : Bounds (121938829 / 250000000) (487755317 / 1000000000) (Real.log (203582037077 / 125000000000)) := by
  have h := reflection_log_12005_neg
  have he : Real.log (203582037077 / 125000000000) = -Real.log (125000000000 / 203582037077) := by
    rw [show ((203582037077 / 125000000000) : ℝ) = ((125000000000 / 203582037077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12006_neg : (489887797 / 1000000000) ≤ -Real.log (20000000000 / 32642661613) ∧
    -Real.log (20000000000 / 32642661613) ≤ (244943899 / 500000000) := by
  have h := checkLog_sound (w := (12642661613 / 52642661613)) (n := 12)
    (lo := (489887797 / 1000000000)) (hi := (244943899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32642661613 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32642661613 / 20000000000) = 1/(20000000000 / 32642661613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12006 : Bounds (489887797 / 1000000000) (244943899 / 500000000) (Real.log (32642661613 / 20000000000)) := by
  have h := reflection_log_12006_neg
  have he : Real.log (32642661613 / 20000000000) = -Real.log (20000000000 / 32642661613) := by
    rw [show ((32642661613 / 20000000000) : ℝ) = ((20000000000 / 32642661613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12007_neg : (497311287 / 500000000) ≤ -Real.log (500000000000 / 1351851851851) ∧
    -Real.log (500000000000 / 1351851851851) ≤ (62163911 / 62500000) := by
  have h := checkLog_sound (w := (351851851851 / 2351851851851)) (n := 12)
    (lo := (150737697 / 500000000)) (hi := (60295079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351851851851 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1351851851851 / 1000000000000) = 1/(500000000000 / 1351851851851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12007 : Bounds (497311287 / 500000000) (62163911 / 62500000) (Real.log (1351851851851 / 500000000000)) := by
  have h := reflection_log_12007_neg
  have he : Real.log (1351851851851 / 500000000000) = -Real.log (500000000000 / 1351851851851) := by
    rw [show ((1351851851851 / 500000000000) : ℝ) = ((500000000000 / 1351851851851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12008_neg : (24929021 / 25000000) ≤ -Real.log (250000000000 / 677643784787) ∧
    -Real.log (250000000000 / 677643784787) ≤ (498580421 / 500000000) := by
  have h := checkLog_sound (w := (177643784787 / 1177643784787)) (n := 12)
    (lo := (15200683 / 50000000)) (hi := (304013661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677643784787 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(677643784787 / 500000000000) = 1/(250000000000 / 677643784787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12008 : Bounds (24929021 / 25000000) (498580421 / 500000000) (Real.log (677643784787 / 250000000000)) := by
  have h := reflection_log_12008_neg
  have he : Real.log (677643784787 / 250000000000) = -Real.log (250000000000 / 677643784787) := by
    rw [show ((677643784787 / 250000000000) : ℝ) = ((250000000000 / 677643784787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12009_neg : (379805361 / 1000000000) ≤ -Real.log (500 / 731) ∧
    -Real.log (500 / 731) ≤ (189902681 / 500000000) := by
  have h := checkLog_sound (w := (231 / 1231)) (n := 12)
    (lo := (379805361 / 1000000000)) (hi := (189902681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731 / 500) = 1/(500 / 731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12009 : Bounds (379805361 / 1000000000) (189902681 / 500000000) (Real.log (731 / 500)) := by
  have h := reflection_log_12009_neg
  have he : Real.log (731 / 500) = -Real.log (500 / 731) := by
    rw [show ((731 / 500) : ℝ) = ((500 / 731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12010_neg : (309948359 / 500000000) ≤ -Real.log (269 / 500) ∧
    -Real.log (269 / 500) ≤ (619896719 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 769)) (n := 12)
    (lo := (309948359 / 500000000)) (hi := (619896719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 269) = 1/(269 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12010 : Bounds (-619896719 / 1000000000) (-309948359 / 500000000) (Real.log (269 / 500)) := by
  have h := reflection_log_12010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12011_neg : (461893 / 1000000000) ≤ -Real.log (500000 / 500231) ∧
    -Real.log (500000 / 500231) ≤ (230947 / 500000000) := by
  have h := checkLog_sound (w := (231 / 1000231)) (n := 12)
    (lo := (461893 / 1000000000)) (hi := (230947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500231 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500231 / 500000) = 1/(500000 / 500231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12011 : Bounds (461893 / 1000000000) (230947 / 500000000) (Real.log (500231 / 500000)) := by
  have h := reflection_log_12011_neg
  have he : Real.log (500231 / 500000) = -Real.log (500000 / 500231) := by
    rw [show ((500231 / 500000) : ℝ) = ((500000 / 500231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12012_neg : (231053 / 500000000) ≤ -Real.log (499769 / 500000) ∧
    -Real.log (499769 / 500000) ≤ (462107 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 999769)) (n := 12)
    (lo := (231053 / 500000000)) (hi := (462107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499769) = 1/(499769 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12012 : Bounds (-462107 / 1000000000) (-231053 / 500000000) (Real.log (499769 / 500000)) := by
  have h := reflection_log_12012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12013_neg : (107441967 / 500000000) ≤ -Real.log (500000 / 619859) ∧
    -Real.log (500000 / 619859) ≤ (42976787 / 200000000) := by
  have h := checkLog_sound (w := (119859 / 1119859)) (n := 12)
    (lo := (107441967 / 500000000)) (hi := (42976787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619859 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619859 / 500000) = 1/(500000 / 619859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12013 : Bounds (107441967 / 500000000) (42976787 / 200000000) (Real.log (619859 / 500000)) := by
  have h := reflection_log_12013_neg
  have he : Real.log (619859 / 500000) = -Real.log (500000 / 619859) := by
    rw [show ((619859 / 500000) : ℝ) = ((500000 / 619859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12014_neg : (274065861 / 1000000000) ≤ -Real.log (380141 / 500000) ∧
    -Real.log (380141 / 500000) ≤ (137032931 / 500000000) := by
  have h := checkLog_sound (w := (119859 / 880141)) (n := 12)
    (lo := (274065861 / 1000000000)) (hi := (137032931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380141) = 1/(380141 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12014 : Bounds (-137032931 / 500000000) (-274065861 / 1000000000) (Real.log (380141 / 500000)) := by
  have h := reflection_log_12014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12015_neg : (107847943 / 500000000) ≤ -Real.log (40000 / 49629) ∧
    -Real.log (40000 / 49629) ≤ (215695887 / 1000000000) := by
  have h := checkLog_sound (w := (9629 / 89629)) (n := 12)
    (lo := (107847943 / 500000000)) (hi := (215695887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49629 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49629 / 40000) = 1/(40000 / 49629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12015 : Bounds (107847943 / 500000000) (215695887 / 1000000000) (Real.log (49629 / 40000)) := by
  have h := reflection_log_12015_neg
  have he : Real.log (49629 / 40000) = -Real.log (40000 / 49629) := by
    rw [show ((49629 / 40000) : ℝ) = ((40000 / 49629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12016_neg : (17211953 / 62500000) ≤ -Real.log (30371 / 40000) ∧
    -Real.log (30371 / 40000) ≤ (275391249 / 1000000000) := by
  have h := checkLog_sound (w := (9629 / 70371)) (n := 12)
    (lo := (17211953 / 62500000)) (hi := (275391249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 30371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 30371) = 1/(30371 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12016 : Bounds (-275391249 / 1000000000) (-17211953 / 62500000) (Real.log (30371 / 40000)) := by
  have h := reflection_log_12016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12017_neg : (29847681 / 500000000) ≤ -Real.log (1507282359 / 1600000000) ∧
    -Real.log (1507282359 / 1600000000) ≤ (59695363 / 1000000000) := by
  have h := checkLog_sound (w := (92717641 / 3107282359)) (n := 12)
    (lo := (29847681 / 500000000)) (hi := (59695363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1507282359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1507282359) = 1/(1507282359 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12017 : Bounds (-59695363 / 1000000000) (-29847681 / 500000000) (Real.log (1507282359 / 1600000000)) := by
  have h := reflection_log_12017_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12018_neg : (59181927 / 1000000000) ≤ -Real.log (235633820119 / 250000000000) ∧
    -Real.log (235633820119 / 250000000000) ≤ (7397741 / 125000000) := by
  have h := checkLog_sound (w := (14366179881 / 485633820119)) (n := 12)
    (lo := (59181927 / 1000000000)) (hi := (7397741 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235633820119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235633820119) = 1/(235633820119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12018 : Bounds (-7397741 / 125000000) (-59181927 / 1000000000) (Real.log (235633820119 / 250000000000)) := by
  have h := reflection_log_12018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12019_neg : (122237449 / 250000000) ≤ -Real.log (125000000000 / 203825356907) ∧
    -Real.log (125000000000 / 203825356907) ≤ (488949797 / 1000000000) := by
  have h := checkLog_sound (w := (78825356907 / 328825356907)) (n := 12)
    (lo := (122237449 / 250000000)) (hi := (488949797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203825356907 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203825356907 / 125000000000) = 1/(125000000000 / 203825356907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12019 : Bounds (122237449 / 250000000) (488949797 / 1000000000) (Real.log (203825356907 / 125000000000)) := by
  have h := reflection_log_12019_neg
  have he : Real.log (203825356907 / 125000000000) = -Real.log (125000000000 / 203825356907) := by
    rw [show ((203825356907 / 125000000000) : ℝ) = ((125000000000 / 203825356907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12020_neg : (245543567 / 500000000) ≤ -Real.log (500000000000 / 817045866123) ∧
    -Real.log (500000000000 / 817045866123) ≤ (98217427 / 200000000) := by
  have h := checkLog_sound (w := (317045866123 / 1317045866123)) (n := 12)
    (lo := (245543567 / 500000000)) (hi := (98217427 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817045866123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817045866123 / 500000000000) = 1/(500000000000 / 817045866123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12020 : Bounds (245543567 / 500000000) (98217427 / 200000000) (Real.log (817045866123 / 500000000000)) := by
  have h := reflection_log_12020_neg
  have he : Real.log (817045866123 / 500000000000) = -Real.log (500000000000 / 817045866123) := by
    rw [show ((817045866123 / 500000000000) : ℝ) = ((500000000000 / 817045866123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12021_neg : (24929021 / 25000000) ≤ -Real.log (500000000000 / 1355287569573) ∧
    -Real.log (500000000000 / 1355287569573) ≤ (498580421 / 500000000) := by
  have h := checkLog_sound (w := (355287569573 / 2355287569573)) (n := 12)
    (lo := (15200683 / 50000000)) (hi := (304013661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355287569573 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1355287569573 / 1000000000000) = 1/(500000000000 / 1355287569573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12021 : Bounds (24929021 / 25000000) (498580421 / 500000000) (Real.log (1355287569573 / 500000000000)) := by
  have h := reflection_log_12021_neg
  have he : Real.log (1355287569573 / 500000000000) = -Real.log (500000000000 / 1355287569573) := by
    rw [show ((1355287569573 / 500000000000) : ℝ) = ((500000000000 / 1355287569573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12022_neg : (999702079 / 1000000000) ≤ -Real.log (12500000000 / 33968401487) ∧
    -Real.log (12500000000 / 33968401487) ≤ (999702081 / 1000000000) := by
  have h := checkLog_sound (w := (8968401487 / 58968401487)) (n := 12)
    (lo := (306554899 / 1000000000)) (hi := (3065549 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33968401487 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(33968401487 / 25000000000) = 1/(12500000000 / 33968401487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12022 : Bounds (999702079 / 1000000000) (999702081 / 1000000000) (Real.log (33968401487 / 12500000000)) := by
  have h := reflection_log_12022_neg
  have he : Real.log (33968401487 / 12500000000) = -Real.log (12500000000 / 33968401487) := by
    rw [show ((33968401487 / 12500000000) : ℝ) = ((12500000000 / 33968401487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12023_neg : (190244561 / 500000000) ≤ -Real.log (1000 / 1463) ∧
    -Real.log (1000 / 1463) ≤ (380489123 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2463)) (n := 12)
    (lo := (190244561 / 500000000)) (hi := (380489123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463 / 1000) = 1/(1000 / 1463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12023 : Bounds (190244561 / 500000000) (380489123 / 1000000000) (Real.log (1463 / 1000)) := by
  have h := reflection_log_12023_neg
  have he : Real.log (1463 / 1000) = -Real.log (1000 / 1463) := by
    rw [show ((1463 / 1000) : ℝ) = ((1000 / 1463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12024_neg : (2428739 / 3906250) ≤ -Real.log (537 / 1000) ∧
    -Real.log (537 / 1000) ≤ (124351437 / 200000000) := by
  have h := checkLog_sound (w := (463 / 1537)) (n := 12)
    (lo := (2428739 / 3906250)) (hi := (124351437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 537) = 1/(537 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12024 : Bounds (-124351437 / 200000000) (-2428739 / 3906250) (Real.log (537 / 1000)) := by
  have h := reflection_log_12024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12025_neg : (115723 / 250000000) ≤ -Real.log (1000000 / 1000463) ∧
    -Real.log (1000000 / 1000463) ≤ (462893 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2000463)) (n := 12)
    (lo := (115723 / 250000000)) (hi := (462893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000463 / 1000000) = 1/(1000000 / 1000463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12025 : Bounds (115723 / 250000000) (462893 / 1000000000) (Real.log (1000463 / 1000000)) := by
  have h := reflection_log_12025_neg
  have he : Real.log (1000463 / 1000000) = -Real.log (1000000 / 1000463) := by
    rw [show ((1000463 / 1000000) : ℝ) = ((1000000 / 1000463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12026_neg : (463107 / 1000000000) ≤ -Real.log (999537 / 1000000) ∧
    -Real.log (999537 / 1000000) ≤ (115777 / 250000000) := by
  have h := checkLog_sound (w := (463 / 1999537)) (n := 12)
    (lo := (463107 / 1000000000)) (hi := (115777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999537) = 1/(999537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12026 : Bounds (-115777 / 250000000) (-463107 / 1000000000) (Real.log (999537 / 1000000)) := by
  have h := reflection_log_12026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12027_neg : (215338773 / 1000000000) ≤ -Real.log (500000 / 620141) ∧
    -Real.log (500000 / 620141) ≤ (107669387 / 500000000) := by
  have h := checkLog_sound (w := (120141 / 1120141)) (n := 12)
    (lo := (215338773 / 1000000000)) (hi := (107669387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620141 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620141 / 500000) = 1/(500000 / 620141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12027 : Bounds (215338773 / 1000000000) (107669387 / 500000000) (Real.log (620141 / 500000)) := by
  have h := reflection_log_12027_neg
  have he : Real.log (620141 / 500000) = -Real.log (500000 / 620141) := by
    rw [show ((620141 / 500000) : ℝ) = ((500000 / 620141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12028_neg : (274807967 / 1000000000) ≤ -Real.log (379859 / 500000) ∧
    -Real.log (379859 / 500000) ≤ (8587749 / 31250000) := by
  have h := checkLog_sound (w := (120141 / 879859)) (n := 12)
    (lo := (274807967 / 1000000000)) (hi := (8587749 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379859) = 1/(379859 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12028 : Bounds (-8587749 / 31250000) (-274807967 / 1000000000) (Real.log (379859 / 500000)) := by
  have h := reflection_log_12028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12029_neg : (216151161 / 1000000000) ≤ -Real.log (100000 / 124129) ∧
    -Real.log (100000 / 124129) ≤ (108075581 / 500000000) := by
  have h := checkLog_sound (w := (24129 / 224129)) (n := 12)
    (lo := (216151161 / 1000000000)) (hi := (108075581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124129 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124129 / 100000) = 1/(100000 / 124129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12029 : Bounds (216151161 / 1000000000) (108075581 / 500000000) (Real.log (124129 / 100000)) := by
  have h := reflection_log_12029_neg
  have he : Real.log (124129 / 100000) = -Real.log (100000 / 124129) := by
    rw [show ((124129 / 100000) : ℝ) = ((100000 / 124129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12030_neg : (34516957 / 125000000) ≤ -Real.log (75871 / 100000) ∧
    -Real.log (75871 / 100000) ≤ (276135657 / 1000000000) := by
  have h := checkLog_sound (w := (24129 / 175871)) (n := 12)
    (lo := (34516957 / 125000000)) (hi := (276135657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 75871) = 1/(75871 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12030 : Bounds (-276135657 / 1000000000) (-34516957 / 125000000) (Real.log (75871 / 100000)) := by
  have h := reflection_log_12030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12031_neg : (29992247 / 500000000) ≤ -Real.log (9417791359 / 10000000000) ∧
    -Real.log (9417791359 / 10000000000) ≤ (11996899 / 200000000) := by
  have h := checkLog_sound (w := (582208641 / 19417791359)) (n := 12)
    (lo := (29992247 / 500000000)) (hi := (11996899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9417791359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9417791359) = 1/(9417791359 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12031 : Bounds (-11996899 / 200000000) (-29992247 / 500000000) (Real.log (9417791359 / 10000000000)) := by
  have h := reflection_log_12031_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

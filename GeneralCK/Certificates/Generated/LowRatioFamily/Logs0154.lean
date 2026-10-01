import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9856_neg : (3059913 / 125000000) ≤ -Real.log (243954470991 / 250000000000) ∧
    -Real.log (243954470991 / 250000000000) ≤ (4895861 / 200000000) := by
  have h := checkLog_sound (w := (6045529009 / 493954470991)) (n := 12)
    (lo := (3059913 / 125000000)) (hi := (4895861 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243954470991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243954470991) = 1/(243954470991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9856 : Bounds (-4895861 / 200000000) (-3059913 / 125000000) (Real.log (243954470991 / 250000000000)) := by
  have h := reflection_log_9856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9857_neg : (31355599 / 100000000) ≤ -Real.log (500000000000 / 684141035933) ∧
    -Real.log (500000000000 / 684141035933) ≤ (313555991 / 1000000000) := by
  have h := checkLog_sound (w := (184141035933 / 1184141035933)) (n := 12)
    (lo := (31355599 / 100000000)) (hi := (313555991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684141035933 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684141035933 / 500000000000) = 1/(500000000000 / 684141035933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9857 : Bounds (31355599 / 100000000) (313555991 / 1000000000) (Real.log (684141035933 / 500000000000)) := by
  have h := reflection_log_9857_neg
  have he : Real.log (684141035933 / 500000000000) = -Real.log (500000000000 / 684141035933) := by
    rw [show ((684141035933 / 500000000000) : ℝ) = ((500000000000 / 684141035933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9858_neg : (315255303 / 1000000000) ≤ -Real.log (31250000000 / 42831537103) ∧
    -Real.log (31250000000 / 42831537103) ≤ (39406913 / 125000000) := by
  have h := checkLog_sound (w := (11581537103 / 74081537103)) (n := 12)
    (lo := (315255303 / 1000000000)) (hi := (39406913 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42831537103 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42831537103 / 31250000000) = 1/(31250000000 / 42831537103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9858 : Bounds (315255303 / 1000000000) (39406913 / 125000000) (Real.log (42831537103 / 31250000000)) := by
  have h := reflection_log_9858_neg
  have he : Real.log (42831537103 / 31250000000) = -Real.log (31250000000 / 42831537103) := by
    rw [show ((42831537103 / 31250000000) : ℝ) = ((31250000000 / 42831537103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9859_neg : (632252349 / 1000000000) ≤ -Real.log (500000000000 / 940922190201) ∧
    -Real.log (500000000000 / 940922190201) ≤ (12645047 / 20000000) := by
  have h := checkLog_sound (w := (440922190201 / 1440922190201)) (n := 12)
    (lo := (632252349 / 1000000000)) (hi := (12645047 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940922190201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940922190201 / 500000000000) = 1/(500000000000 / 940922190201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9859 : Bounds (632252349 / 1000000000) (12645047 / 20000000) (Real.log (940922190201 / 500000000000)) := by
  have h := reflection_log_9859_neg
  have he : Real.log (940922190201 / 500000000000) = -Real.log (500000000000 / 940922190201) := by
    rw [show ((940922190201 / 500000000000) : ℝ) = ((500000000000 / 940922190201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9860_neg : (317229857 / 500000000) ≤ -Real.log (250000000000 / 471500721501) ∧
    -Real.log (250000000000 / 471500721501) ≤ (126891943 / 200000000) := by
  have h := checkLog_sound (w := (221500721501 / 721500721501)) (n := 12)
    (lo := (317229857 / 500000000)) (hi := (126891943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471500721501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471500721501 / 250000000000) = 1/(250000000000 / 471500721501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9860 : Bounds (317229857 / 500000000) (126891943 / 200000000) (Real.log (471500721501 / 250000000000)) := by
  have h := reflection_log_9860_neg
  have he : Real.log (471500721501 / 250000000000) = -Real.log (250000000000 / 471500721501) := by
    rw [show ((471500721501 / 250000000000) : ℝ) = ((250000000000 / 471500721501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9861_neg : (268499253 / 1000000000) ≤ -Real.log (250 / 327) ∧
    -Real.log (250 / 327) ≤ (134249627 / 500000000) := by
  have h := checkLog_sound (w := (77 / 577)) (n := 12)
    (lo := (268499253 / 1000000000)) (hi := (134249627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327 / 250) = 1/(250 / 327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9861 : Bounds (268499253 / 1000000000) (134249627 / 500000000) (Real.log (327 / 250)) := by
  have h := reflection_log_9861_neg
  have he : Real.log (327 / 250) = -Real.log (250 / 327) := by
    rw [show ((327 / 250) : ℝ) = ((250 / 327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9862_neg : (368169323 / 1000000000) ≤ -Real.log (173 / 250) ∧
    -Real.log (173 / 250) ≤ (92042331 / 250000000) := by
  have h := checkLog_sound (w := (77 / 423)) (n := 12)
    (lo := (368169323 / 1000000000)) (hi := (92042331 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 173) = 1/(173 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9862 : Bounds (-92042331 / 250000000) (-368169323 / 1000000000) (Real.log (173 / 250)) := by
  have h := reflection_log_9862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9863_neg : (19247 / 62500000) ≤ -Real.log (250000 / 250077) ∧
    -Real.log (250000 / 250077) ≤ (307953 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 500077)) (n := 12)
    (lo := (19247 / 62500000)) (hi := (307953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250077 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250077 / 250000) = 1/(250000 / 250077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9863 : Bounds (19247 / 62500000) (307953 / 1000000000) (Real.log (250077 / 250000)) := by
  have h := reflection_log_9863_neg
  have he : Real.log (250077 / 250000) = -Real.log (250000 / 250077) := by
    rw [show ((250077 / 250000) : ℝ) = ((250000 / 250077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9864_neg : (308047 / 1000000000) ≤ -Real.log (249923 / 250000) ∧
    -Real.log (249923 / 250000) ≤ (19253 / 62500000) := by
  have h := checkLog_sound (w := (77 / 499923)) (n := 12)
    (lo := (308047 / 1000000000)) (hi := (19253 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249923) = 1/(249923 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9864 : Bounds (-19253 / 62500000) (-308047 / 1000000000) (Real.log (249923 / 250000)) := by
  have h := reflection_log_9864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9865_neg : (36248579 / 250000000) ≤ -Real.log (1000000 / 1156033) ∧
    -Real.log (1000000 / 1156033) ≤ (144994317 / 1000000000) := by
  have h := checkLog_sound (w := (156033 / 2156033)) (n := 12)
    (lo := (36248579 / 250000000)) (hi := (144994317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156033 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1156033 / 1000000) = 1/(1000000 / 1156033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9865 : Bounds (36248579 / 250000000) (144994317 / 1000000000) (Real.log (1156033 / 1000000)) := by
  have h := reflection_log_9865_neg
  have he : Real.log (1156033 / 1000000) = -Real.log (1000000 / 1156033) := by
    rw [show ((1156033 / 1000000) : ℝ) = ((1000000 / 1156033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9866_neg : (42410471 / 250000000) ≤ -Real.log (843967 / 1000000) ∧
    -Real.log (843967 / 1000000) ≤ (33928377 / 200000000) := by
  have h := checkLog_sound (w := (156033 / 1843967)) (n := 12)
    (lo := (42410471 / 250000000)) (hi := (33928377 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 843967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 843967) = 1/(843967 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9866 : Bounds (-33928377 / 200000000) (-42410471 / 250000000) (Real.log (843967 / 1000000)) := by
  have h := reflection_log_9866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9867_neg : (145711167 / 1000000000) ≤ -Real.log (500000 / 578431) ∧
    -Real.log (500000 / 578431) ≤ (2276737 / 15625000) := by
  have h := checkLog_sound (w := (78431 / 1078431)) (n := 12)
    (lo := (145711167 / 1000000000)) (hi := (2276737 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(578431 / 500000) = 1/(500000 / 578431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9867 : Bounds (145711167 / 1000000000) (2276737 / 15625000) (Real.log (578431 / 500000)) := by
  have h := reflection_log_9867_neg
  have he : Real.log (578431 / 500000) = -Real.log (500000 / 578431) := by
    rw [show ((578431 / 500000) : ℝ) = ((500000 / 578431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9868_neg : (170624633 / 1000000000) ≤ -Real.log (421569 / 500000) ∧
    -Real.log (421569 / 500000) ≤ (85312317 / 500000000) := by
  have h := checkLog_sound (w := (78431 / 921569)) (n := 12)
    (lo := (170624633 / 1000000000)) (hi := (85312317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 421569) = 1/(421569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9868 : Bounds (-85312317 / 500000000) (-170624633 / 1000000000) (Real.log (421569 / 500000)) := by
  have h := reflection_log_9868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9869_neg : (12456733 / 500000000) ≤ -Real.log (243848578239 / 250000000000) ∧
    -Real.log (243848578239 / 250000000000) ≤ (24913467 / 1000000000) := by
  have h := checkLog_sound (w := (6151421761 / 493848578239)) (n := 12)
    (lo := (12456733 / 500000000)) (hi := (24913467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243848578239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243848578239) = 1/(243848578239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9869 : Bounds (-24913467 / 1000000000) (-12456733 / 500000000) (Real.log (243848578239 / 250000000000)) := by
  have h := reflection_log_9869_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9870_neg : (1540473 / 62500000) ≤ -Real.log (975653702911 / 1000000000000) ∧
    -Real.log (975653702911 / 1000000000000) ≤ (24647569 / 1000000000) := by
  have h := checkLog_sound (w := (24346297089 / 1975653702911)) (n := 12)
    (lo := (1540473 / 62500000)) (hi := (24647569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975653702911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975653702911) = 1/(975653702911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9870 : Bounds (-24647569 / 1000000000) (-1540473 / 62500000) (Real.log (975653702911 / 1000000000000)) := by
  have h := reflection_log_9870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9871_neg : (314636201 / 1000000000) ≤ -Real.log (250000000000 / 342440225743) ∧
    -Real.log (250000000000 / 342440225743) ≤ (157318101 / 500000000) := by
  have h := checkLog_sound (w := (92440225743 / 592440225743)) (n := 12)
    (lo := (314636201 / 1000000000)) (hi := (157318101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342440225743 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342440225743 / 250000000000) = 1/(250000000000 / 342440225743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9871 : Bounds (314636201 / 1000000000) (157318101 / 500000000) (Real.log (342440225743 / 250000000000)) := by
  have h := reflection_log_9871_neg
  have he : Real.log (342440225743 / 250000000000) = -Real.log (250000000000 / 342440225743) := by
    rw [show ((342440225743 / 250000000000) : ℝ) = ((250000000000 / 342440225743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9872_neg : (1581679 / 5000000) ≤ -Real.log (100000000000 / 137209092699) ∧
    -Real.log (100000000000 / 137209092699) ≤ (316335801 / 1000000000) := by
  have h := checkLog_sound (w := (37209092699 / 237209092699)) (n := 12)
    (lo := (1581679 / 5000000)) (hi := (316335801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137209092699 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137209092699 / 100000000000) = 1/(100000000000 / 137209092699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9872 : Bounds (1581679 / 5000000) (316335801 / 1000000000) (Real.log (137209092699 / 100000000000)) := by
  have h := reflection_log_9872_neg
  have he : Real.log (137209092699 / 100000000000) = -Real.log (100000000000 / 137209092699) := by
    rw [show ((137209092699 / 100000000000) : ℝ) = ((100000000000 / 137209092699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9873_neg : (317229857 / 500000000) ≤ -Real.log (500000000000 / 943001443001) ∧
    -Real.log (500000000000 / 943001443001) ≤ (126891943 / 200000000) := by
  have h := checkLog_sound (w := (443001443001 / 1443001443001)) (n := 12)
    (lo := (317229857 / 500000000)) (hi := (126891943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((943001443001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(943001443001 / 500000000000) = 1/(500000000000 / 943001443001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9873 : Bounds (317229857 / 500000000) (126891943 / 200000000) (Real.log (943001443001 / 500000000000)) := by
  have h := reflection_log_9873_neg
  have he : Real.log (943001443001 / 500000000000) = -Real.log (500000000000 / 943001443001) := by
    rw [show ((943001443001 / 500000000000) : ℝ) = ((500000000000 / 943001443001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9874_neg : (19895893 / 31250000) ≤ -Real.log (500000000000 / 945086705203) ∧
    -Real.log (500000000000 / 945086705203) ≤ (636668577 / 1000000000) := by
  have h := checkLog_sound (w := (445086705203 / 1445086705203)) (n := 12)
    (lo := (19895893 / 31250000)) (hi := (636668577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((945086705203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(945086705203 / 500000000000) = 1/(500000000000 / 945086705203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9874 : Bounds (19895893 / 31250000) (636668577 / 1000000000) (Real.log (945086705203 / 500000000000)) := by
  have h := reflection_log_9874_neg
  have he : Real.log (945086705203 / 500000000000) = -Real.log (500000000000 / 945086705203) := by
    rw [show ((945086705203 / 500000000000) : ℝ) = ((500000000000 / 945086705203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9875_neg : (134631743 / 500000000) ≤ -Real.log (1000 / 1309) ∧
    -Real.log (1000 / 1309) ≤ (269263487 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 2309)) (n := 12)
    (lo := (134631743 / 500000000)) (hi := (269263487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1309 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1309 / 1000) = 1/(1000 / 1309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9875 : Bounds (134631743 / 500000000) (269263487 / 1000000000) (Real.log (1309 / 1000)) := by
  have h := reflection_log_9875_neg
  have he : Real.log (1309 / 1000) = -Real.log (1000 / 1309) := by
    rw [show ((1309 / 1000) : ℝ) = ((1000 / 1309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9876_neg : (73923091 / 200000000) ≤ -Real.log (691 / 1000) ∧
    -Real.log (691 / 1000) ≤ (11550483 / 31250000) := by
  have h := checkLog_sound (w := (309 / 1691)) (n := 12)
    (lo := (73923091 / 200000000)) (hi := (11550483 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 691) = 1/(691 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9876 : Bounds (-11550483 / 31250000) (-73923091 / 200000000) (Real.log (691 / 1000)) := by
  have h := reflection_log_9876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9877_neg : (38619 / 125000000) ≤ -Real.log (1000000 / 1000309) ∧
    -Real.log (1000000 / 1000309) ≤ (308953 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 2000309)) (n := 12)
    (lo := (38619 / 125000000)) (hi := (308953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000309 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000309 / 1000000) = 1/(1000000 / 1000309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9877 : Bounds (38619 / 125000000) (308953 / 1000000000) (Real.log (1000309 / 1000000)) := by
  have h := reflection_log_9877_neg
  have he : Real.log (1000309 / 1000000) = -Real.log (1000000 / 1000309) := by
    rw [show ((1000309 / 1000000) : ℝ) = ((1000000 / 1000309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9878_neg : (309047 / 1000000000) ≤ -Real.log (999691 / 1000000) ∧
    -Real.log (999691 / 1000000) ≤ (38631 / 125000000) := by
  have h := checkLog_sound (w := (309 / 1999691)) (n := 12)
    (lo := (309047 / 1000000000)) (hi := (38631 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999691) = 1/(999691 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9878 : Bounds (-38631 / 125000000) (-309047 / 1000000000) (Real.log (999691 / 1000000)) := by
  have h := reflection_log_9878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9879_neg : (145449217 / 1000000000) ≤ -Real.log (1000000 / 1156559) ∧
    -Real.log (1000000 / 1156559) ≤ (72724609 / 500000000) := by
  have h := checkLog_sound (w := (156559 / 2156559)) (n := 12)
    (lo := (145449217 / 1000000000)) (hi := (72724609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1156559 / 1000000) = 1/(1000000 / 1156559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9879 : Bounds (145449217 / 1000000000) (72724609 / 500000000) (Real.log (1156559 / 1000000)) := by
  have h := reflection_log_9879_neg
  have he : Real.log (1156559 / 1000000) = -Real.log (1000000 / 1156559) := by
    rw [show ((1156559 / 1000000) : ℝ) = ((1000000 / 1156559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9880_neg : (85132663 / 500000000) ≤ -Real.log (843441 / 1000000) ∧
    -Real.log (843441 / 1000000) ≤ (170265327 / 1000000000) := by
  have h := checkLog_sound (w := (156559 / 1843441)) (n := 12)
    (lo := (85132663 / 500000000)) (hi := (170265327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 843441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 843441) = 1/(843441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9880 : Bounds (-170265327 / 1000000000) (-85132663 / 500000000) (Real.log (843441 / 1000000)) := by
  have h := reflection_log_9880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9881_neg : (14616747 / 100000000) ≤ -Real.log (100000 / 115739) ∧
    -Real.log (100000 / 115739) ≤ (146167471 / 1000000000) := by
  have h := checkLog_sound (w := (15739 / 215739)) (n := 12)
    (lo := (14616747 / 100000000)) (hi := (146167471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115739 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115739 / 100000) = 1/(100000 / 115739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9881 : Bounds (14616747 / 100000000) (146167471 / 1000000000) (Real.log (115739 / 100000)) := by
  have h := reflection_log_9881_neg
  have he : Real.log (115739 / 100000) = -Real.log (100000 / 115739) := by
    rw [show ((115739 / 100000) : ℝ) = ((100000 / 115739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9882_neg : (171251061 / 1000000000) ≤ -Real.log (84261 / 100000) ∧
    -Real.log (84261 / 100000) ≤ (85625531 / 500000000) := by
  have h := checkLog_sound (w := (15739 / 184261)) (n := 12)
    (lo := (171251061 / 1000000000)) (hi := (85625531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 84261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 84261) = 1/(84261 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9882 : Bounds (-85625531 / 500000000) (-171251061 / 1000000000) (Real.log (84261 / 100000)) := by
  have h := reflection_log_9882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9883_neg : (25083591 / 1000000000) ≤ -Real.log (9752283879 / 10000000000) ∧
    -Real.log (9752283879 / 10000000000) ≤ (3135449 / 125000000) := by
  have h := checkLog_sound (w := (247716121 / 19752283879)) (n := 12)
    (lo := (25083591 / 1000000000)) (hi := (3135449 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9752283879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9752283879) = 1/(9752283879 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9883 : Bounds (-3135449 / 125000000) (-25083591 / 1000000000) (Real.log (9752283879 / 10000000000)) := by
  have h := reflection_log_9883_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9884_neg : (6204027 / 250000000) ≤ -Real.log (975489279519 / 1000000000000) ∧
    -Real.log (975489279519 / 1000000000000) ≤ (24816109 / 1000000000) := by
  have h := checkLog_sound (w := (24510720481 / 1975489279519)) (n := 12)
    (lo := (6204027 / 250000000)) (hi := (24816109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975489279519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975489279519) = 1/(975489279519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9884 : Bounds (-24816109 / 1000000000) (-6204027 / 250000000) (Real.log (975489279519 / 1000000000000)) := by
  have h := reflection_log_9884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9885_neg : (315714543 / 1000000000) ≤ -Real.log (500000000000 / 685619385351) ∧
    -Real.log (500000000000 / 685619385351) ≤ (19732159 / 62500000) := by
  have h := checkLog_sound (w := (185619385351 / 1185619385351)) (n := 12)
    (lo := (315714543 / 1000000000)) (hi := (19732159 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685619385351 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685619385351 / 500000000000) = 1/(500000000000 / 685619385351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9885 : Bounds (315714543 / 1000000000) (19732159 / 62500000) (Real.log (685619385351 / 500000000000)) := by
  have h := reflection_log_9885_neg
  have he : Real.log (685619385351 / 500000000000) = -Real.log (500000000000 / 685619385351) := by
    rw [show ((685619385351 / 500000000000) : ℝ) = ((500000000000 / 685619385351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9886_neg : (317418531 / 1000000000) ≤ -Real.log (250000000000 / 343394334271) ∧
    -Real.log (250000000000 / 343394334271) ≤ (79354633 / 250000000) := by
  have h := checkLog_sound (w := (93394334271 / 593394334271)) (n := 12)
    (lo := (317418531 / 1000000000)) (hi := (79354633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343394334271 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343394334271 / 250000000000) = 1/(250000000000 / 343394334271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9886 : Bounds (317418531 / 1000000000) (79354633 / 250000000) (Real.log (343394334271 / 250000000000)) := by
  have h := reflection_log_9886_neg
  have he : Real.log (343394334271 / 250000000000) = -Real.log (250000000000 / 343394334271) := by
    rw [show ((343394334271 / 250000000000) : ℝ) = ((250000000000 / 343394334271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9887_neg : (19895893 / 31250000) ≤ -Real.log (250000000000 / 472543352601) ∧
    -Real.log (250000000000 / 472543352601) ≤ (636668577 / 1000000000) := by
  have h := checkLog_sound (w := (222543352601 / 722543352601)) (n := 12)
    (lo := (19895893 / 31250000)) (hi := (636668577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((472543352601 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(472543352601 / 250000000000) = 1/(250000000000 / 472543352601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9887 : Bounds (19895893 / 31250000) (636668577 / 1000000000) (Real.log (472543352601 / 250000000000)) := by
  have h := reflection_log_9887_neg
  have he : Real.log (472543352601 / 250000000000) = -Real.log (250000000000 / 472543352601) := by
    rw [show ((472543352601 / 250000000000) : ℝ) = ((250000000000 / 472543352601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9888_neg : (319439471 / 500000000) ≤ -Real.log (100000000000 / 189435600579) ∧
    -Real.log (100000000000 / 189435600579) ≤ (638878943 / 1000000000) := by
  have h := checkLog_sound (w := (89435600579 / 289435600579)) (n := 12)
    (lo := (319439471 / 500000000)) (hi := (638878943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189435600579 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189435600579 / 100000000000) = 1/(100000000000 / 189435600579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9888 : Bounds (319439471 / 500000000) (638878943 / 1000000000) (Real.log (189435600579 / 100000000000)) := by
  have h := reflection_log_9888_neg
  have he : Real.log (189435600579 / 100000000000) = -Real.log (100000000000 / 189435600579) := by
    rw [show ((189435600579 / 100000000000) : ℝ) = ((100000000000 / 189435600579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9889_neg : (270027137 / 1000000000) ≤ -Real.log (100 / 131) ∧
    -Real.log (100 / 131) ≤ (135013569 / 500000000) := by
  have h := checkLog_sound (w := (31 / 231)) (n := 12)
    (lo := (270027137 / 1000000000)) (hi := (135013569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131 / 100) = 1/(100 / 131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9889 : Bounds (270027137 / 1000000000) (135013569 / 500000000) (Real.log (131 / 100)) := by
  have h := reflection_log_9889_neg
  have he : Real.log (131 / 100) = -Real.log (100 / 131) := by
    rw [show ((131 / 100) : ℝ) = ((100 / 131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9890_neg : (371063681 / 1000000000) ≤ -Real.log (69 / 100) ∧
    -Real.log (69 / 100) ≤ (185531841 / 500000000) := by
  have h := checkLog_sound (w := (31 / 169)) (n := 12)
    (lo := (371063681 / 1000000000)) (hi := (185531841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 69) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 69) = 1/(69 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9890 : Bounds (-185531841 / 500000000) (-371063681 / 1000000000) (Real.log (69 / 100)) := by
  have h := reflection_log_9890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9891_neg : (309951 / 1000000000) ≤ -Real.log (100000 / 100031) ∧
    -Real.log (100000 / 100031) ≤ (4843 / 15625000) := by
  have h := checkLog_sound (w := (31 / 200031)) (n := 12)
    (lo := (309951 / 1000000000)) (hi := (4843 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100031 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100031 / 100000) = 1/(100000 / 100031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9891 : Bounds (309951 / 1000000000) (4843 / 15625000) (Real.log (100031 / 100000)) := by
  have h := reflection_log_9891_neg
  have he : Real.log (100031 / 100000) = -Real.log (100000 / 100031) := by
    rw [show ((100031 / 100000) : ℝ) = ((100000 / 100031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9892_neg : (9689 / 31250000) ≤ -Real.log (99969 / 100000) ∧
    -Real.log (99969 / 100000) ≤ (310049 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 199969)) (n := 12)
    (lo := (9689 / 31250000)) (hi := (310049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99969) = 1/(99969 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9892 : Bounds (-310049 / 1000000000) (-9689 / 31250000) (Real.log (99969 / 100000)) := by
  have h := reflection_log_9892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9893_neg : (145903911 / 1000000000) ≤ -Real.log (200000 / 231417) ∧
    -Real.log (200000 / 231417) ≤ (18237989 / 125000000) := by
  have h := checkLog_sound (w := (31417 / 431417)) (n := 12)
    (lo := (145903911 / 1000000000)) (hi := (18237989 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231417 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231417 / 200000) = 1/(200000 / 231417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9893 : Bounds (145903911 / 1000000000) (18237989 / 125000000) (Real.log (231417 / 200000)) := by
  have h := reflection_log_9893_neg
  have he : Real.log (231417 / 200000) = -Real.log (200000 / 231417) := by
    rw [show ((231417 / 200000) : ℝ) = ((200000 / 231417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9894_neg : (42722289 / 250000000) ≤ -Real.log (168583 / 200000) ∧
    -Real.log (168583 / 200000) ≤ (170889157 / 1000000000) := by
  have h := checkLog_sound (w := (31417 / 368583)) (n := 12)
    (lo := (42722289 / 250000000)) (hi := (170889157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168583) = 1/(168583 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9894 : Bounds (-170889157 / 1000000000) (-42722289 / 250000000) (Real.log (168583 / 200000)) := by
  have h := reflection_log_9894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9895_neg : (146622701 / 1000000000) ≤ -Real.log (1000000 / 1157917) ∧
    -Real.log (1000000 / 1157917) ≤ (73311351 / 500000000) := by
  have h := checkLog_sound (w := (157917 / 2157917)) (n := 12)
    (lo := (146622701 / 1000000000)) (hi := (73311351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157917 / 1000000) = 1/(1000000 / 1157917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9895 : Bounds (146622701 / 1000000000) (73311351 / 500000000) (Real.log (1157917 / 1000000)) := by
  have h := reflection_log_9895_neg
  have he : Real.log (1157917 / 1000000) = -Real.log (1000000 / 1157917) := by
    rw [show ((1157917 / 1000000) : ℝ) = ((1000000 / 1157917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9896_neg : (85938347 / 500000000) ≤ -Real.log (842083 / 1000000) ∧
    -Real.log (842083 / 1000000) ≤ (34375339 / 200000000) := by
  have h := checkLog_sound (w := (157917 / 1842083)) (n := 12)
    (lo := (85938347 / 500000000)) (hi := (34375339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 842083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 842083) = 1/(842083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9896 : Bounds (-34375339 / 200000000) (-85938347 / 500000000) (Real.log (842083 / 1000000)) := by
  have h := reflection_log_9896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9897_neg : (25253993 / 1000000000) ≤ -Real.log (975062221111 / 1000000000000) ∧
    -Real.log (975062221111 / 1000000000000) ≤ (12626997 / 500000000) := by
  have h := checkLog_sound (w := (24937778889 / 1975062221111)) (n := 12)
    (lo := (25253993 / 1000000000)) (hi := (12626997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975062221111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975062221111) = 1/(975062221111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9897 : Bounds (-12626997 / 500000000) (-25253993 / 1000000000) (Real.log (975062221111 / 1000000000000)) := by
  have h := reflection_log_9897_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9898_neg : (4997049 / 200000000) ≤ -Real.log (39012972111 / 40000000000) ∧
    -Real.log (39012972111 / 40000000000) ≤ (12492623 / 500000000) := by
  have h := checkLog_sound (w := (987027889 / 79012972111)) (n := 12)
    (lo := (4997049 / 200000000)) (hi := (12492623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39012972111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39012972111) = 1/(39012972111 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9898 : Bounds (-12492623 / 500000000) (-4997049 / 200000000) (Real.log (39012972111 / 40000000000)) := by
  have h := reflection_log_9898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9899_neg : (316793067 / 1000000000) ≤ -Real.log (500000000000 / 686359241441) ∧
    -Real.log (500000000000 / 686359241441) ≤ (79198267 / 250000000) := by
  have h := checkLog_sound (w := (186359241441 / 1186359241441)) (n := 12)
    (lo := (316793067 / 1000000000)) (hi := (79198267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686359241441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686359241441 / 500000000000) = 1/(500000000000 / 686359241441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9899 : Bounds (316793067 / 1000000000) (79198267 / 250000000) (Real.log (686359241441 / 500000000000)) := by
  have h := reflection_log_9899_neg
  have he : Real.log (686359241441 / 500000000000) = -Real.log (500000000000 / 686359241441) := by
    rw [show ((686359241441 / 500000000000) : ℝ) = ((500000000000 / 686359241441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9900_neg : (79624849 / 250000000) ≤ -Real.log (250000000000 / 343765697681) ∧
    -Real.log (250000000000 / 343765697681) ≤ (318499397 / 1000000000) := by
  have h := checkLog_sound (w := (93765697681 / 593765697681)) (n := 12)
    (lo := (79624849 / 250000000)) (hi := (318499397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343765697681 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343765697681 / 250000000000) = 1/(250000000000 / 343765697681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9900 : Bounds (79624849 / 250000000) (318499397 / 1000000000) (Real.log (343765697681 / 250000000000)) := by
  have h := reflection_log_9900_neg
  have he : Real.log (343765697681 / 250000000000) = -Real.log (250000000000 / 343765697681) := by
    rw [show ((343765697681 / 250000000000) : ℝ) = ((250000000000 / 343765697681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9901_neg : (319439471 / 500000000) ≤ -Real.log (250000000000 / 473589001447) ∧
    -Real.log (250000000000 / 473589001447) ≤ (638878943 / 1000000000) := by
  have h := checkLog_sound (w := (223589001447 / 723589001447)) (n := 12)
    (lo := (319439471 / 500000000)) (hi := (638878943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473589001447 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473589001447 / 250000000000) = 1/(250000000000 / 473589001447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9901 : Bounds (319439471 / 500000000) (638878943 / 1000000000) (Real.log (473589001447 / 250000000000)) := by
  have h := reflection_log_9901_neg
  have he : Real.log (473589001447 / 250000000000) = -Real.log (250000000000 / 473589001447) := by
    rw [show ((473589001447 / 250000000000) : ℝ) = ((250000000000 / 473589001447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9902_neg : (320545409 / 500000000) ≤ -Real.log (500000000000 / 949275362319) ∧
    -Real.log (500000000000 / 949275362319) ≤ (641090819 / 1000000000) := by
  have h := checkLog_sound (w := (449275362319 / 1449275362319)) (n := 12)
    (lo := (320545409 / 500000000)) (hi := (641090819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((949275362319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(949275362319 / 500000000000) = 1/(500000000000 / 949275362319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9902 : Bounds (320545409 / 500000000) (641090819 / 1000000000) (Real.log (949275362319 / 500000000000)) := by
  have h := reflection_log_9902_neg
  have he : Real.log (949275362319 / 500000000000) = -Real.log (500000000000 / 949275362319) := by
    rw [show ((949275362319 / 500000000000) : ℝ) = ((500000000000 / 949275362319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9903_neg : (67697551 / 250000000) ≤ -Real.log (1000 / 1311) ∧
    -Real.log (1000 / 1311) ≤ (54158041 / 200000000) := by
  have h := checkLog_sound (w := (311 / 2311)) (n := 12)
    (lo := (67697551 / 250000000)) (hi := (54158041 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311 / 1000) = 1/(1000 / 1311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9903 : Bounds (67697551 / 250000000) (54158041 / 200000000) (Real.log (1311 / 1000)) := by
  have h := reflection_log_9903_neg
  have he : Real.log (1311 / 1000) = -Real.log (1000 / 1311) := by
    rw [show ((1311 / 1000) : ℝ) = ((1000 / 1311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9904_neg : (372514007 / 1000000000) ≤ -Real.log (689 / 1000) ∧
    -Real.log (689 / 1000) ≤ (46564251 / 125000000) := by
  have h := checkLog_sound (w := (311 / 1689)) (n := 12)
    (lo := (372514007 / 1000000000)) (hi := (46564251 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 689) = 1/(689 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9904 : Bounds (-46564251 / 125000000) (-372514007 / 1000000000) (Real.log (689 / 1000)) := by
  have h := reflection_log_9904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9905_neg : (310951 / 1000000000) ≤ -Real.log (1000000 / 1000311) ∧
    -Real.log (1000000 / 1000311) ≤ (38869 / 125000000) := by
  have h := checkLog_sound (w := (311 / 2000311)) (n := 12)
    (lo := (310951 / 1000000000)) (hi := (38869 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000311 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000311 / 1000000) = 1/(1000000 / 1000311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9905 : Bounds (310951 / 1000000000) (38869 / 125000000) (Real.log (1000311 / 1000000)) := by
  have h := reflection_log_9905_neg
  have he : Real.log (1000311 / 1000000) = -Real.log (1000000 / 1000311) := by
    rw [show ((1000311 / 1000000) : ℝ) = ((1000000 / 1000311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9906_neg : (38881 / 125000000) ≤ -Real.log (999689 / 1000000) ∧
    -Real.log (999689 / 1000000) ≤ (311049 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 1999689)) (n := 12)
    (lo := (38881 / 125000000)) (hi := (311049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999689) = 1/(999689 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9906 : Bounds (-311049 / 1000000000) (-38881 / 125000000) (Real.log (999689 / 1000000)) := by
  have h := reflection_log_9906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9907_neg : (73179631 / 500000000) ≤ -Real.log (250000 / 289403) ∧
    -Real.log (250000 / 289403) ≤ (146359263 / 1000000000) := by
  have h := checkLog_sound (w := (39403 / 539403)) (n := 12)
    (lo := (73179631 / 500000000)) (hi := (146359263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289403 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289403 / 250000) = 1/(250000 / 289403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9907 : Bounds (73179631 / 500000000) (146359263 / 1000000000) (Real.log (289403 / 250000)) := by
  have h := reflection_log_9907_neg
  have he : Real.log (289403 / 250000) = -Real.log (250000 / 289403) := by
    rw [show ((289403 / 250000) : ℝ) = ((250000 / 289403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9908_neg : (171514563 / 1000000000) ≤ -Real.log (210597 / 250000) ∧
    -Real.log (210597 / 250000) ≤ (42878641 / 250000000) := by
  have h := checkLog_sound (w := (39403 / 460597)) (n := 12)
    (lo := (171514563 / 1000000000)) (hi := (42878641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 210597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 210597) = 1/(210597 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9908 : Bounds (-42878641 / 250000000) (-171514563 / 1000000000) (Real.log (210597 / 250000)) := by
  have h := reflection_log_9908_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9909_neg : (36769647 / 250000000) ≤ -Real.log (200000 / 231689) ∧
    -Real.log (200000 / 231689) ≤ (147078589 / 1000000000) := by
  have h := checkLog_sound (w := (31689 / 431689)) (n := 12)
    (lo := (36769647 / 250000000)) (hi := (147078589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231689 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231689 / 200000) = 1/(200000 / 231689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9909 : Bounds (36769647 / 250000000) (147078589 / 1000000000) (Real.log (231689 / 200000)) := by
  have h := reflection_log_9909_neg
  have he : Real.log (231689 / 200000) = -Real.log (200000 / 231689) := by
    rw [show ((231689 / 200000) : ℝ) = ((200000 / 231689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9910_neg : (43125977 / 250000000) ≤ -Real.log (168311 / 200000) ∧
    -Real.log (168311 / 200000) ≤ (172503909 / 1000000000) := by
  have h := checkLog_sound (w := (31689 / 368311)) (n := 12)
    (lo := (43125977 / 250000000)) (hi := (172503909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168311) = 1/(168311 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9910 : Bounds (-172503909 / 1000000000) (-43125977 / 250000000) (Real.log (168311 / 200000)) := by
  have h := reflection_log_9910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9911_neg : (25425319 / 1000000000) ≤ -Real.log (38995807279 / 40000000000) ∧
    -Real.log (38995807279 / 40000000000) ≤ (635633 / 25000000) := by
  have h := checkLog_sound (w := (1004192721 / 78995807279)) (n := 12)
    (lo := (25425319 / 1000000000)) (hi := (635633 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38995807279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38995807279) = 1/(38995807279 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9911 : Bounds (-635633 / 25000000) (-25425319 / 1000000000) (Real.log (38995807279 / 40000000000)) := by
  have h := reflection_log_9911_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9912_neg : (251553 / 10000000) ≤ -Real.log (60947403591 / 62500000000) ∧
    -Real.log (60947403591 / 62500000000) ≤ (25155301 / 1000000000) := by
  have h := checkLog_sound (w := (1552596409 / 123447403591)) (n := 12)
    (lo := (251553 / 10000000)) (hi := (25155301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60947403591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60947403591) = 1/(60947403591 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9912 : Bounds (-25155301 / 1000000000) (-251553 / 10000000) (Real.log (60947403591 / 62500000000)) := by
  have h := reflection_log_9912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9913_neg : (12714953 / 40000000) ≤ -Real.log (250000000000 / 343550715347) ∧
    -Real.log (250000000000 / 343550715347) ≤ (158936913 / 500000000) := by
  have h := checkLog_sound (w := (93550715347 / 593550715347)) (n := 12)
    (lo := (12714953 / 40000000)) (hi := (158936913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343550715347 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343550715347 / 250000000000) = 1/(250000000000 / 343550715347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9913 : Bounds (12714953 / 40000000) (158936913 / 500000000) (Real.log (343550715347 / 250000000000)) := by
  have h := reflection_log_9913_neg
  have he : Real.log (343550715347 / 250000000000) = -Real.log (250000000000 / 343550715347) := by
    rw [show ((343550715347 / 250000000000) : ℝ) = ((250000000000 / 343550715347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9914_neg : (9986953 / 31250000) ≤ -Real.log (500000000000 / 688276464403) ∧
    -Real.log (500000000000 / 688276464403) ≤ (319582497 / 1000000000) := by
  have h := checkLog_sound (w := (188276464403 / 1188276464403)) (n := 12)
    (lo := (9986953 / 31250000)) (hi := (319582497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688276464403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688276464403 / 500000000000) = 1/(500000000000 / 688276464403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9914 : Bounds (9986953 / 31250000) (319582497 / 1000000000) (Real.log (688276464403 / 500000000000)) := by
  have h := reflection_log_9914_neg
  have he : Real.log (688276464403 / 500000000000) = -Real.log (500000000000 / 688276464403) := by
    rw [show ((688276464403 / 500000000000) : ℝ) = ((500000000000 / 688276464403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9915_neg : (320545409 / 500000000) ≤ -Real.log (250000000000 / 474637681159) ∧
    -Real.log (250000000000 / 474637681159) ≤ (641090819 / 1000000000) := by
  have h := checkLog_sound (w := (224637681159 / 724637681159)) (n := 12)
    (lo := (320545409 / 500000000)) (hi := (641090819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((474637681159 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(474637681159 / 250000000000) = 1/(250000000000 / 474637681159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9915 : Bounds (320545409 / 500000000) (641090819 / 1000000000) (Real.log (474637681159 / 250000000000)) := by
  have h := reflection_log_9915_neg
  have he : Real.log (474637681159 / 250000000000) = -Real.log (250000000000 / 474637681159) := by
    rw [show ((474637681159 / 250000000000) : ℝ) = ((250000000000 / 474637681159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9916_neg : (160826053 / 250000000) ≤ -Real.log (50000000000 / 95137880987) ∧
    -Real.log (50000000000 / 95137880987) ≤ (643304213 / 1000000000) := by
  have h := checkLog_sound (w := (45137880987 / 145137880987)) (n := 12)
    (lo := (160826053 / 250000000)) (hi := (643304213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95137880987 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95137880987 / 50000000000) = 1/(50000000000 / 95137880987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9916 : Bounds (160826053 / 250000000) (643304213 / 1000000000) (Real.log (95137880987 / 50000000000)) := by
  have h := reflection_log_9916_neg
  have he : Real.log (95137880987 / 50000000000) = -Real.log (50000000000 / 95137880987) := by
    rw [show ((95137880987 / 50000000000) : ℝ) = ((50000000000 / 95137880987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9917_neg : (27155269 / 100000000) ≤ -Real.log (125 / 164) ∧
    -Real.log (125 / 164) ≤ (271552691 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 289)) (n := 12)
    (lo := (27155269 / 100000000)) (hi := (271552691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164 / 125) = 1/(125 / 164) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9917 : Bounds (27155269 / 100000000) (271552691 / 1000000000) (Real.log (164 / 125)) := by
  have h := reflection_log_9917_neg
  have he : Real.log (164 / 125) = -Real.log (125 / 164) := by
    rw [show ((164 / 125) : ℝ) = ((125 / 164) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9918_neg : (373966441 / 1000000000) ≤ -Real.log (86 / 125) ∧
    -Real.log (86 / 125) ≤ (186983221 / 500000000) := by
  have h := checkLog_sound (w := (39 / 211)) (n := 12)
    (lo := (373966441 / 1000000000)) (hi := (186983221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 86) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 86) = 1/(86 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9918 : Bounds (-186983221 / 500000000) (-373966441 / 1000000000) (Real.log (86 / 125)) := by
  have h := reflection_log_9918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9919_neg : (311951 / 1000000000) ≤ -Real.log (125000 / 125039) ∧
    -Real.log (125000 / 125039) ≤ (19497 / 62500000) := by
  have h := checkLog_sound (w := (39 / 250039)) (n := 12)
    (lo := (311951 / 1000000000)) (hi := (19497 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125039 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125039 / 125000) = 1/(125000 / 125039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9919 : Bounds (311951 / 1000000000) (19497 / 62500000) (Real.log (125039 / 125000)) := by
  have h := reflection_log_9919_neg
  have he : Real.log (125039 / 125000) = -Real.log (125000 / 125039) := by
    rw [show ((125039 / 125000) : ℝ) = ((125000 / 125039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

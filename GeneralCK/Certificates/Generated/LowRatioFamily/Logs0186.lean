import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11904_neg : (269467633 / 1000000000) ≤ -Real.log (381893 / 500000) ∧
    -Real.log (381893 / 500000) ≤ (134733817 / 500000000) := by
  have h := checkLog_sound (w := (118107 / 881893)) (n := 12)
    (lo := (269467633 / 1000000000)) (hi := (134733817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381893) = 1/(381893 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11904 : Bounds (-134733817 / 500000000) (-269467633 / 1000000000) (Real.log (381893 / 500000)) := by
  have h := reflection_log_11904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11905_neg : (1148283 / 20000000) ≤ -Real.log (236050736551 / 250000000000) ∧
    -Real.log (236050736551 / 250000000000) ≤ (57414151 / 1000000000) := by
  have h := checkLog_sound (w := (13949263449 / 486050736551)) (n := 12)
    (lo := (1148283 / 20000000)) (hi := (57414151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236050736551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236050736551) = 1/(236050736551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11905 : Bounds (-57414151 / 1000000000) (-1148283 / 20000000) (Real.log (236050736551 / 250000000000)) := by
  have h := reflection_log_11905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11906_neg : (28458241 / 500000000) ≤ -Real.log (944672962911 / 1000000000000) ∧
    -Real.log (944672962911 / 1000000000000) ≤ (56916483 / 1000000000) := by
  have h := checkLog_sound (w := (55327037089 / 1944672962911)) (n := 12)
    (lo := (28458241 / 500000000)) (hi := (56916483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 944672962911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 944672962911) = 1/(944672962911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11906 : Bounds (-56916483 / 1000000000) (-28458241 / 500000000) (Real.log (944672962911 / 1000000000000)) := by
  have h := reflection_log_11906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11907_neg : (29963113 / 62500000) ≤ -Real.log (2000000000 / 3230241781) ∧
    -Real.log (2000000000 / 3230241781) ≤ (479409809 / 1000000000) := by
  have h := checkLog_sound (w := (1230241781 / 5230241781)) (n := 12)
    (lo := (29963113 / 62500000)) (hi := (479409809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3230241781 / 2000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3230241781 / 2000000000) = 1/(2000000000 / 3230241781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11907 : Bounds (29963113 / 62500000) (479409809 / 1000000000) (Real.log (3230241781 / 2000000000)) := by
  have h := reflection_log_11907_neg
  have he : Real.log (3230241781 / 2000000000) = -Real.log (2000000000 / 3230241781) := by
    rw [show ((3230241781 / 2000000000) : ℝ) = ((2000000000 / 3230241781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11908_neg : (120380279 / 250000000) ≤ -Real.log (7812500000 / 12644800867) ∧
    -Real.log (7812500000 / 12644800867) ≤ (481521117 / 1000000000) := by
  have h := checkLog_sound (w := (4832300867 / 20457300867)) (n := 12)
    (lo := (120380279 / 250000000)) (hi := (481521117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12644800867 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12644800867 / 7812500000) = 1/(7812500000 / 12644800867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11908 : Bounds (120380279 / 250000000) (481521117 / 1000000000) (Real.log (12644800867 / 7812500000)) := by
  have h := reflection_log_11908_neg
  have he : Real.log (12644800867 / 7812500000) = -Real.log (7812500000 / 12644800867) := by
    rw [show ((12644800867 / 7812500000) : ℝ) = ((7812500000 / 12644800867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11909_neg : (48846843 / 50000000) ≤ -Real.log (500000000000 / 1328153564899) ∧
    -Real.log (500000000000 / 1328153564899) ≤ (488468431 / 500000000) := by
  have h := checkLog_sound (w := (328153564899 / 2328153564899)) (n := 12)
    (lo := (3547371 / 12500000)) (hi := (283789681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328153564899 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1328153564899 / 1000000000000) = 1/(500000000000 / 1328153564899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11909 : Bounds (48846843 / 50000000) (488468431 / 500000000) (Real.log (1328153564899 / 500000000000)) := by
  have h := reflection_log_11909_neg
  have he : Real.log (1328153564899 / 500000000000) = -Real.log (500000000000 / 1328153564899) := by
    rw [show ((1328153564899 / 500000000000) : ℝ) = ((500000000000 / 1328153564899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11910_neg : (979454681 / 1000000000) ≤ -Real.log (250000000000 / 665750915751) ∧
    -Real.log (250000000000 / 665750915751) ≤ (979454683 / 1000000000) := by
  have h := checkLog_sound (w := (165750915751 / 1165750915751)) (n := 12)
    (lo := (286307501 / 1000000000)) (hi := (143153751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665750915751 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(665750915751 / 500000000000) = 1/(250000000000 / 665750915751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11910 : Bounds (979454681 / 1000000000) (979454683 / 1000000000) (Real.log (665750915751 / 250000000000)) := by
  have h := reflection_log_11910_neg
  have he : Real.log (665750915751 / 250000000000) = -Real.log (250000000000 / 665750915751) := by
    rw [show ((665750915751 / 250000000000) : ℝ) = ((250000000000 / 665750915751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11911_neg : (3750059 / 10000000) ≤ -Real.log (200 / 291) ∧
    -Real.log (200 / 291) ≤ (375005901 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 491)) (n := 12)
    (lo := (3750059 / 10000000)) (hi := (375005901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291 / 200) = 1/(200 / 291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11911 : Bounds (3750059 / 10000000) (375005901 / 1000000000) (Real.log (291 / 200)) := by
  have h := reflection_log_11911_neg
  have he : Real.log (291 / 200) = -Real.log (200 / 291) := by
    rw [show ((291 / 200) : ℝ) = ((200 / 291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11912_neg : (151742371 / 250000000) ≤ -Real.log (109 / 200) ∧
    -Real.log (109 / 200) ≤ (121393897 / 200000000) := by
  have h := checkLog_sound (w := (91 / 309)) (n := 12)
    (lo := (151742371 / 250000000)) (hi := (121393897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 109) = 1/(109 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11912 : Bounds (-121393897 / 200000000) (-151742371 / 250000000) (Real.log (109 / 200)) := by
  have h := reflection_log_11912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11913_neg : (28431 / 62500000) ≤ -Real.log (200000 / 200091) ∧
    -Real.log (200000 / 200091) ≤ (454897 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 400091)) (n := 12)
    (lo := (28431 / 62500000)) (hi := (454897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200091 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200091 / 200000) = 1/(200000 / 200091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11913 : Bounds (28431 / 62500000) (454897 / 1000000000) (Real.log (200091 / 200000)) := by
  have h := reflection_log_11913_neg
  have he : Real.log (200091 / 200000) = -Real.log (200000 / 200091) := by
    rw [show ((200091 / 200000) : ℝ) = ((200000 / 200091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11914_neg : (455103 / 1000000000) ≤ -Real.log (199909 / 200000) ∧
    -Real.log (199909 / 200000) ≤ (7111 / 15625000) := by
  have h := checkLog_sound (w := (91 / 399909)) (n := 12)
    (lo := (455103 / 1000000000)) (hi := (7111 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199909) = 1/(199909 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11914 : Bounds (-7111 / 15625000) (-455103 / 1000000000) (Real.log (199909 / 200000)) := by
  have h := reflection_log_11914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11915_neg : (10585077 / 50000000) ≤ -Real.log (1000000 / 1235779) ∧
    -Real.log (1000000 / 1235779) ≤ (211701541 / 1000000000) := by
  have h := checkLog_sound (w := (235779 / 2235779)) (n := 12)
    (lo := (10585077 / 50000000)) (hi := (211701541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235779 / 1000000) = 1/(1000000 / 1235779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11915 : Bounds (10585077 / 50000000) (211701541 / 1000000000) (Real.log (1235779 / 1000000)) := by
  have h := reflection_log_11915_neg
  have he : Real.log (1235779 / 1000000) = -Real.log (1000000 / 1235779) := by
    rw [show ((1235779 / 1000000) : ℝ) = ((1000000 / 1235779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11916_neg : (33612283 / 125000000) ≤ -Real.log (764221 / 1000000) ∧
    -Real.log (764221 / 1000000) ≤ (53779653 / 200000000) := by
  have h := checkLog_sound (w := (235779 / 1764221)) (n := 12)
    (lo := (33612283 / 125000000)) (hi := (53779653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764221) = 1/(764221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11916 : Bounds (-53779653 / 200000000) (-33612283 / 125000000) (Real.log (764221 / 1000000)) := by
  have h := reflection_log_11916_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11917_neg : (106254401 / 500000000) ≤ -Real.log (1000000 / 1236777) ∧
    -Real.log (1000000 / 1236777) ≤ (212508803 / 1000000000) := by
  have h := checkLog_sound (w := (236777 / 2236777)) (n := 12)
    (lo := (106254401 / 500000000)) (hi := (212508803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236777 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236777 / 1000000) = 1/(1000000 / 1236777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11917 : Bounds (106254401 / 500000000) (212508803 / 1000000000) (Real.log (1236777 / 1000000)) := by
  have h := reflection_log_11917_neg
  have he : Real.log (1236777 / 1000000) = -Real.log (1000000 / 1236777) := by
    rw [show ((1236777 / 1000000) : ℝ) = ((1000000 / 1236777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11918_neg : (270205023 / 1000000000) ≤ -Real.log (763223 / 1000000) ∧
    -Real.log (763223 / 1000000) ≤ (8443907 / 31250000) := by
  have h := checkLog_sound (w := (236777 / 1763223)) (n := 12)
    (lo := (270205023 / 1000000000)) (hi := (8443907 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763223) = 1/(763223 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11918 : Bounds (-8443907 / 31250000) (-270205023 / 1000000000) (Real.log (763223 / 1000000)) := by
  have h := reflection_log_11918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11919_neg : (2884811 / 50000000) ≤ -Real.log (943936652271 / 1000000000000) ∧
    -Real.log (943936652271 / 1000000000000) ≤ (57696221 / 1000000000) := by
  have h := checkLog_sound (w := (56063347729 / 1943936652271)) (n := 12)
    (lo := (2884811 / 50000000)) (hi := (57696221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 943936652271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 943936652271) = 1/(943936652271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11919 : Bounds (-57696221 / 1000000000) (-2884811 / 50000000) (Real.log (943936652271 / 1000000000000)) := by
  have h := reflection_log_11919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11920_neg : (14299181 / 250000000) ≤ -Real.log (944408263159 / 1000000000000) ∧
    -Real.log (944408263159 / 1000000000000) ≤ (2287869 / 40000000) := by
  have h := checkLog_sound (w := (55591736841 / 1944408263159)) (n := 12)
    (lo := (14299181 / 250000000)) (hi := (2287869 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 944408263159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 944408263159) = 1/(944408263159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11920 : Bounds (-2287869 / 40000000) (-14299181 / 250000000) (Real.log (944408263159 / 1000000000000)) := by
  have h := reflection_log_11920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11921_neg : (96119961 / 200000000) ≤ -Real.log (500000000000 / 808522011303) ∧
    -Real.log (500000000000 / 808522011303) ≤ (240299903 / 500000000) := by
  have h := checkLog_sound (w := (308522011303 / 1308522011303)) (n := 12)
    (lo := (96119961 / 200000000)) (hi := (240299903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808522011303 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808522011303 / 500000000000) = 1/(500000000000 / 808522011303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11921 : Bounds (96119961 / 200000000) (240299903 / 500000000) (Real.log (808522011303 / 500000000000)) := by
  have h := reflection_log_11921_neg
  have he : Real.log (808522011303 / 500000000000) = -Real.log (500000000000 / 808522011303) := by
    rw [show ((808522011303 / 500000000000) : ℝ) = ((500000000000 / 808522011303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11922_neg : (19308553 / 40000000) ≤ -Real.log (500000000000 / 810233051153) ∧
    -Real.log (500000000000 / 810233051153) ≤ (241356913 / 500000000) := by
  have h := checkLog_sound (w := (310233051153 / 1310233051153)) (n := 12)
    (lo := (19308553 / 40000000)) (hi := (241356913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((810233051153 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(810233051153 / 500000000000) = 1/(500000000000 / 810233051153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11922 : Bounds (19308553 / 40000000) (241356913 / 500000000) (Real.log (810233051153 / 500000000000)) := by
  have h := reflection_log_11922_neg
  have he : Real.log (810233051153 / 500000000000) = -Real.log (500000000000 / 810233051153) := by
    rw [show ((810233051153 / 500000000000) : ℝ) = ((500000000000 / 810233051153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11923_neg : (979454681 / 1000000000) ≤ -Real.log (500000000000 / 1331501831501) ∧
    -Real.log (500000000000 / 1331501831501) ≤ (979454683 / 1000000000) := by
  have h := checkLog_sound (w := (331501831501 / 2331501831501)) (n := 12)
    (lo := (286307501 / 1000000000)) (hi := (143153751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331501831501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1331501831501 / 1000000000000) = 1/(500000000000 / 1331501831501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11923 : Bounds (979454681 / 1000000000) (979454683 / 1000000000) (Real.log (1331501831501 / 500000000000)) := by
  have h := reflection_log_11923_neg
  have he : Real.log (1331501831501 / 500000000000) = -Real.log (500000000000 / 1331501831501) := by
    rw [show ((1331501831501 / 500000000000) : ℝ) = ((500000000000 / 1331501831501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11924_neg : (122746923 / 125000000) ≤ -Real.log (250000000000 / 667431192661) ∧
    -Real.log (250000000000 / 667431192661) ≤ (490987693 / 500000000) := by
  have h := checkLog_sound (w := (167431192661 / 1167431192661)) (n := 12)
    (lo := (72207051 / 250000000)) (hi := (57765641 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667431192661 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(667431192661 / 500000000000) = 1/(250000000000 / 667431192661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11924 : Bounds (122746923 / 125000000) (490987693 / 500000000) (Real.log (667431192661 / 250000000000)) := by
  have h := reflection_log_11924_neg
  have he : Real.log (667431192661 / 250000000000) = -Real.log (250000000000 / 667431192661) := by
    rw [show ((667431192661 / 250000000000) : ℝ) = ((250000000000 / 667431192661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11925_neg : (375692949 / 1000000000) ≤ -Real.log (125 / 182) ∧
    -Real.log (125 / 182) ≤ (7513859 / 20000000) := by
  have h := checkLog_sound (w := (57 / 307)) (n := 12)
    (lo := (375692949 / 1000000000)) (hi := (7513859 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182 / 125) = 1/(125 / 182) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11925 : Bounds (375692949 / 1000000000) (7513859 / 20000000) (Real.log (182 / 125)) := by
  have h := reflection_log_11925_neg
  have he : Real.log (182 / 125) = -Real.log (125 / 182) := by
    rw [show ((182 / 125) : ℝ) = ((125 / 182) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11926_neg : (38050377 / 62500000) ≤ -Real.log (68 / 125) ∧
    -Real.log (68 / 125) ≤ (608806033 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 193)) (n := 12)
    (lo := (38050377 / 62500000)) (hi := (608806033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 68) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 68) = 1/(68 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11926 : Bounds (-608806033 / 1000000000) (-38050377 / 62500000) (Real.log (68 / 125)) := by
  have h := reflection_log_11926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11927_neg : (56987 / 125000000) ≤ -Real.log (125000 / 125057) ∧
    -Real.log (125000 / 125057) ≤ (455897 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 250057)) (n := 12)
    (lo := (56987 / 125000000)) (hi := (455897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125057 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125057 / 125000) = 1/(125000 / 125057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11927 : Bounds (56987 / 125000000) (455897 / 1000000000) (Real.log (125057 / 125000)) := by
  have h := reflection_log_11927_neg
  have he : Real.log (125057 / 125000) = -Real.log (125000 / 125057) := by
    rw [show ((125057 / 125000) : ℝ) = ((125000 / 125057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11928_neg : (456103 / 1000000000) ≤ -Real.log (124943 / 125000) ∧
    -Real.log (124943 / 125000) ≤ (57013 / 125000000) := by
  have h := checkLog_sound (w := (57 / 249943)) (n := 12)
    (lo := (456103 / 1000000000)) (hi := (57013 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124943) = 1/(124943 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11928 : Bounds (-57013 / 125000000) (-456103 / 1000000000) (Real.log (124943 / 125000)) := by
  have h := reflection_log_11928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11929_neg : (106077701 / 500000000) ≤ -Real.log (50000 / 61817) ∧
    -Real.log (50000 / 61817) ≤ (212155403 / 1000000000) := by
  have h := checkLog_sound (w := (11817 / 111817)) (n := 12)
    (lo := (106077701 / 500000000)) (hi := (212155403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61817 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61817 / 50000) = 1/(50000 / 61817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11929 : Bounds (106077701 / 500000000) (212155403 / 1000000000) (Real.log (61817 / 50000)) := by
  have h := reflection_log_11929_neg
  have he : Real.log (61817 / 50000) = -Real.log (50000 / 61817) := by
    rw [show ((61817 / 50000) : ℝ) = ((50000 / 61817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11930_neg : (53926523 / 200000000) ≤ -Real.log (38183 / 50000) ∧
    -Real.log (38183 / 50000) ≤ (33704077 / 125000000) := by
  have h := checkLog_sound (w := (11817 / 88183)) (n := 12)
    (lo := (53926523 / 200000000)) (hi := (33704077 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 38183) = 1/(38183 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11930 : Bounds (-33704077 / 125000000) (-53926523 / 200000000) (Real.log (38183 / 50000)) := by
  have h := reflection_log_11930_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11931_neg : (106481957 / 500000000) ≤ -Real.log (50000 / 61867) ∧
    -Real.log (50000 / 61867) ≤ (42592783 / 200000000) := by
  have h := checkLog_sound (w := (11867 / 111867)) (n := 12)
    (lo := (106481957 / 500000000)) (hi := (42592783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61867 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61867 / 50000) = 1/(50000 / 61867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11931 : Bounds (106481957 / 500000000) (42592783 / 200000000) (Real.log (61867 / 50000)) := by
  have h := reflection_log_11931_neg
  have he : Real.log (61867 / 50000) = -Real.log (50000 / 61867) := by
    rw [show ((61867 / 50000) : ℝ) = ((50000 / 61867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11932_neg : (67735739 / 250000000) ≤ -Real.log (38133 / 50000) ∧
    -Real.log (38133 / 50000) ≤ (270942957 / 1000000000) := by
  have h := checkLog_sound (w := (11867 / 88133)) (n := 12)
    (lo := (67735739 / 250000000)) (hi := (270942957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 38133) = 1/(38133 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11932 : Bounds (-270942957 / 1000000000) (-67735739 / 250000000) (Real.log (38133 / 50000)) := by
  have h := reflection_log_11932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11933_neg : (28989521 / 500000000) ≤ -Real.log (2359174311 / 2500000000) ∧
    -Real.log (2359174311 / 2500000000) ≤ (57979043 / 1000000000) := by
  have h := checkLog_sound (w := (140825689 / 4859174311)) (n := 12)
    (lo := (28989521 / 500000000)) (hi := (57979043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2359174311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2359174311) = 1/(2359174311 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11933 : Bounds (-57979043 / 1000000000) (-28989521 / 500000000) (Real.log (2359174311 / 2500000000)) := by
  have h := reflection_log_11933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11934_neg : (14369303 / 250000000) ≤ -Real.log (2360358511 / 2500000000) ∧
    -Real.log (2360358511 / 2500000000) ≤ (57477213 / 1000000000) := by
  have h := checkLog_sound (w := (139641489 / 4860358511)) (n := 12)
    (lo := (14369303 / 250000000)) (hi := (57477213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2360358511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2360358511) = 1/(2360358511 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11934 : Bounds (-57477213 / 1000000000) (-14369303 / 250000000) (Real.log (2360358511 / 2500000000)) := by
  have h := reflection_log_11934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11935_neg : (481788017 / 1000000000) ≤ -Real.log (250000000000 / 404741638949) ∧
    -Real.log (250000000000 / 404741638949) ≤ (240894009 / 500000000) := by
  have h := checkLog_sound (w := (154741638949 / 654741638949)) (n := 12)
    (lo := (481788017 / 1000000000)) (hi := (240894009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((404741638949 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(404741638949 / 250000000000) = 1/(250000000000 / 404741638949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11935 : Bounds (481788017 / 1000000000) (240894009 / 500000000) (Real.log (404741638949 / 250000000000)) := by
  have h := reflection_log_11935_neg
  have he : Real.log (404741638949 / 250000000000) = -Real.log (250000000000 / 404741638949) := by
    rw [show ((404741638949 / 250000000000) : ℝ) = ((250000000000 / 404741638949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11936_neg : (48390687 / 100000000) ≤ -Real.log (50000000000 / 81120027273) ∧
    -Real.log (50000000000 / 81120027273) ≤ (483906871 / 1000000000) := by
  have h := checkLog_sound (w := (31120027273 / 131120027273)) (n := 12)
    (lo := (48390687 / 100000000)) (hi := (483906871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81120027273 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81120027273 / 50000000000) = 1/(50000000000 / 81120027273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11936 : Bounds (48390687 / 100000000) (483906871 / 1000000000) (Real.log (81120027273 / 50000000000)) := by
  have h := reflection_log_11936_neg
  have he : Real.log (81120027273 / 50000000000) = -Real.log (50000000000 / 81120027273) := by
    rw [show ((81120027273 / 50000000000) : ℝ) = ((50000000000 / 81120027273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11937_neg : (122746923 / 125000000) ≤ -Real.log (500000000000 / 1334862385321) ∧
    -Real.log (500000000000 / 1334862385321) ≤ (490987693 / 500000000) := by
  have h := checkLog_sound (w := (334862385321 / 2334862385321)) (n := 12)
    (lo := (72207051 / 250000000)) (hi := (57765641 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1334862385321 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1334862385321 / 1000000000000) = 1/(500000000000 / 1334862385321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11937 : Bounds (122746923 / 125000000) (490987693 / 500000000) (Real.log (1334862385321 / 500000000000)) := by
  have h := reflection_log_11937_neg
  have he : Real.log (1334862385321 / 500000000000) = -Real.log (500000000000 / 1334862385321) := by
    rw [show ((1334862385321 / 500000000000) : ℝ) = ((500000000000 / 1334862385321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11938_neg : (984498981 / 1000000000) ≤ -Real.log (250000000000 / 669117647059) ∧
    -Real.log (250000000000 / 669117647059) ≤ (984498983 / 1000000000) := by
  have h := checkLog_sound (w := (169117647059 / 1169117647059)) (n := 12)
    (lo := (291351801 / 1000000000)) (hi := (145675901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669117647059 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(669117647059 / 500000000000) = 1/(250000000000 / 669117647059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11938 : Bounds (984498981 / 1000000000) (984498983 / 1000000000) (Real.log (669117647059 / 250000000000)) := by
  have h := reflection_log_11938_neg
  have he : Real.log (669117647059 / 250000000000) = -Real.log (250000000000 / 669117647059) := by
    rw [show ((669117647059 / 250000000000) : ℝ) = ((250000000000 / 669117647059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11939_neg : (376379527 / 1000000000) ≤ -Real.log (1000 / 1457) ∧
    -Real.log (1000 / 1457) ≤ (47047441 / 125000000) := by
  have h := checkLog_sound (w := (457 / 2457)) (n := 12)
    (lo := (376379527 / 1000000000)) (hi := (47047441 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1457 / 1000) = 1/(1000 / 1457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11939 : Bounds (376379527 / 1000000000) (47047441 / 125000000) (Real.log (1457 / 1000)) := by
  have h := reflection_log_11939_neg
  have he : Real.log (1457 / 1000) = -Real.log (1000 / 1457) := by
    rw [show ((1457 / 1000) : ℝ) = ((1000 / 1457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11940_neg : (610645959 / 1000000000) ≤ -Real.log (543 / 1000) ∧
    -Real.log (543 / 1000) ≤ (15266149 / 25000000) := by
  have h := checkLog_sound (w := (457 / 1543)) (n := 12)
    (lo := (610645959 / 1000000000)) (hi := (15266149 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 543) = 1/(543 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11940 : Bounds (-15266149 / 25000000) (-610645959 / 1000000000) (Real.log (543 / 1000)) := by
  have h := reflection_log_11940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11941_neg : (91379 / 200000000) ≤ -Real.log (1000000 / 1000457) ∧
    -Real.log (1000000 / 1000457) ≤ (7139 / 15625000) := by
  have h := checkLog_sound (w := (457 / 2000457)) (n := 12)
    (lo := (91379 / 200000000)) (hi := (7139 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000457 / 1000000) = 1/(1000000 / 1000457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11941 : Bounds (91379 / 200000000) (7139 / 15625000) (Real.log (1000457 / 1000000)) := by
  have h := reflection_log_11941_neg
  have he : Real.log (1000457 / 1000000) = -Real.log (1000000 / 1000457) := by
    rw [show ((1000457 / 1000000) : ℝ) = ((1000000 / 1000457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11942_neg : (28569 / 62500000) ≤ -Real.log (999543 / 1000000) ∧
    -Real.log (999543 / 1000000) ≤ (91421 / 200000000) := by
  have h := checkLog_sound (w := (457 / 1999543)) (n := 12)
    (lo := (28569 / 62500000)) (hi := (91421 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999543) = 1/(999543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11942 : Bounds (-91421 / 200000000) (-28569 / 62500000) (Real.log (999543 / 1000000)) := by
  have h := reflection_log_11942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11943_neg : (106305337 / 500000000) ≤ -Real.log (1000000 / 1236903) ∧
    -Real.log (1000000 / 1236903) ≤ (8504427 / 40000000) := by
  have h := checkLog_sound (w := (236903 / 2236903)) (n := 12)
    (lo := (106305337 / 500000000)) (hi := (8504427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236903 / 1000000) = 1/(1000000 / 1236903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11943 : Bounds (106305337 / 500000000) (8504427 / 40000000) (Real.log (1236903 / 1000000)) := by
  have h := reflection_log_11943_neg
  have he : Real.log (1236903 / 1000000) = -Real.log (1000000 / 1236903) := by
    rw [show ((1236903 / 1000000) : ℝ) = ((1000000 / 1236903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11944_neg : (135185063 / 500000000) ≤ -Real.log (763097 / 1000000) ∧
    -Real.log (763097 / 1000000) ≤ (270370127 / 1000000000) := by
  have h := checkLog_sound (w := (236903 / 1763097)) (n := 12)
    (lo := (135185063 / 500000000)) (hi := (270370127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763097) = 1/(763097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11944 : Bounds (-270370127 / 1000000000) (-135185063 / 500000000) (Real.log (763097 / 1000000)) := by
  have h := reflection_log_11944_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11945_neg : (106709813 / 500000000) ≤ -Real.log (62500 / 77369) ∧
    -Real.log (62500 / 77369) ≤ (213419627 / 1000000000) := by
  have h := checkLog_sound (w := (14869 / 139869)) (n := 12)
    (lo := (106709813 / 500000000)) (hi := (213419627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77369 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77369 / 62500) = 1/(62500 / 77369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11945 : Bounds (106709813 / 500000000) (213419627 / 1000000000) (Real.log (77369 / 62500)) := by
  have h := reflection_log_11945_neg
  have he : Real.log (77369 / 62500) = -Real.log (62500 / 77369) := by
    rw [show ((77369 / 62500) : ℝ) = ((62500 / 77369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11946_neg : (135841373 / 500000000) ≤ -Real.log (47631 / 62500) ∧
    -Real.log (47631 / 62500) ≤ (271682747 / 1000000000) := by
  have h := checkLog_sound (w := (14869 / 110131)) (n := 12)
    (lo := (135841373 / 500000000)) (hi := (271682747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 47631) = 1/(47631 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11946 : Bounds (-271682747 / 1000000000) (-135841373 / 500000000) (Real.log (47631 / 62500)) := by
  have h := reflection_log_11946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11947_neg : (728289 / 12500000) ≤ -Real.log (3685162839 / 3906250000) ∧
    -Real.log (3685162839 / 3906250000) ≤ (58263121 / 1000000000) := by
  have h := checkLog_sound (w := (221087161 / 7591412839)) (n := 12)
    (lo := (728289 / 12500000)) (hi := (58263121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3685162839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3685162839) = 1/(3685162839 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11947 : Bounds (-58263121 / 1000000000) (-728289 / 12500000) (Real.log (3685162839 / 3906250000)) := by
  have h := reflection_log_11947_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11948_neg : (57759451 / 1000000000) ≤ -Real.log (943876968591 / 1000000000000) ∧
    -Real.log (943876968591 / 1000000000000) ≤ (14439863 / 250000000) := by
  have h := checkLog_sound (w := (56123031409 / 1943876968591)) (n := 12)
    (lo := (57759451 / 1000000000)) (hi := (14439863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 943876968591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 943876968591) = 1/(943876968591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11948 : Bounds (-14439863 / 250000000) (-57759451 / 1000000000) (Real.log (943876968591 / 1000000000000)) := by
  have h := reflection_log_11948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11949_neg : (301863 / 625000) ≤ -Real.log (50000000000 / 81044939241) ∧
    -Real.log (50000000000 / 81044939241) ≤ (482980801 / 1000000000) := by
  have h := checkLog_sound (w := (31044939241 / 131044939241)) (n := 12)
    (lo := (301863 / 625000)) (hi := (482980801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81044939241 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81044939241 / 50000000000) = 1/(50000000000 / 81044939241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11949 : Bounds (301863 / 625000) (482980801 / 1000000000) (Real.log (81044939241 / 50000000000)) := by
  have h := reflection_log_11949_neg
  have he : Real.log (81044939241 / 50000000000) = -Real.log (50000000000 / 81044939241) := by
    rw [show ((81044939241 / 50000000000) : ℝ) = ((50000000000 / 81044939241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11950_neg : (485102373 / 1000000000) ≤ -Real.log (500000000000 / 812170645169) ∧
    -Real.log (500000000000 / 812170645169) ≤ (242551187 / 500000000) := by
  have h := checkLog_sound (w := (312170645169 / 1312170645169)) (n := 12)
    (lo := (485102373 / 1000000000)) (hi := (242551187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812170645169 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812170645169 / 500000000000) = 1/(500000000000 / 812170645169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11950 : Bounds (485102373 / 1000000000) (242551187 / 500000000) (Real.log (812170645169 / 500000000000)) := by
  have h := reflection_log_11950_neg
  have he : Real.log (812170645169 / 500000000000) = -Real.log (500000000000 / 812170645169) := by
    rw [show ((812170645169 / 500000000000) : ℝ) = ((500000000000 / 812170645169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11951_neg : (984498981 / 1000000000) ≤ -Real.log (500000000000 / 1338235294117) ∧
    -Real.log (500000000000 / 1338235294117) ≤ (984498983 / 1000000000) := by
  have h := checkLog_sound (w := (338235294117 / 2338235294117)) (n := 12)
    (lo := (291351801 / 1000000000)) (hi := (145675901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338235294117 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1338235294117 / 1000000000000) = 1/(500000000000 / 1338235294117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11951 : Bounds (984498981 / 1000000000) (984498983 / 1000000000) (Real.log (1338235294117 / 500000000000)) := by
  have h := reflection_log_11951_neg
  have he : Real.log (1338235294117 / 500000000000) = -Real.log (500000000000 / 1338235294117) := by
    rw [show ((1338235294117 / 500000000000) : ℝ) = ((500000000000 / 1338235294117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11952_neg : (197405097 / 200000000) ≤ -Real.log (62500000000 / 167702578269) ∧
    -Real.log (62500000000 / 167702578269) ≤ (987025487 / 1000000000) := by
  have h := checkLog_sound (w := (42702578269 / 292702578269)) (n := 12)
    (lo := (58775661 / 200000000)) (hi := (146939153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167702578269 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(167702578269 / 125000000000) = 1/(62500000000 / 167702578269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11952 : Bounds (197405097 / 200000000) (987025487 / 1000000000) (Real.log (167702578269 / 62500000000)) := by
  have h := reflection_log_11952_neg
  have he : Real.log (167702578269 / 62500000000) = -Real.log (62500000000 / 167702578269) := by
    rw [show ((167702578269 / 62500000000) : ℝ) = ((62500000000 / 167702578269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11953_neg : (377065633 / 1000000000) ≤ -Real.log (500 / 729) ∧
    -Real.log (500 / 729) ≤ (188532817 / 500000000) := by
  have h := checkLog_sound (w := (229 / 1229)) (n := 12)
    (lo := (377065633 / 1000000000)) (hi := (188532817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729 / 500) = 1/(500 / 729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11953 : Bounds (377065633 / 1000000000) (188532817 / 500000000) (Real.log (729 / 500)) := by
  have h := reflection_log_11953_neg
  have he : Real.log (729 / 500) = -Real.log (500 / 729) := by
    rw [show ((729 / 500) : ℝ) = ((500 / 729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11954_neg : (612489277 / 1000000000) ≤ -Real.log (271 / 500) ∧
    -Real.log (271 / 500) ≤ (306244639 / 500000000) := by
  have h := checkLog_sound (w := (229 / 771)) (n := 12)
    (lo := (612489277 / 1000000000)) (hi := (306244639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 271) = 1/(271 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11954 : Bounds (-306244639 / 500000000) (-612489277 / 1000000000) (Real.log (271 / 500)) := by
  have h := reflection_log_11954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11955_neg : (91579 / 200000000) ≤ -Real.log (500000 / 500229) ∧
    -Real.log (500000 / 500229) ≤ (57237 / 125000000) := by
  have h := checkLog_sound (w := (229 / 1000229)) (n := 12)
    (lo := (91579 / 200000000)) (hi := (57237 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500229 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500229 / 500000) = 1/(500000 / 500229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11955 : Bounds (91579 / 200000000) (57237 / 125000000) (Real.log (500229 / 500000)) := by
  have h := reflection_log_11955_neg
  have he : Real.log (500229 / 500000) = -Real.log (500000 / 500229) := by
    rw [show ((500229 / 500000) : ℝ) = ((500000 / 500229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11956_neg : (57263 / 125000000) ≤ -Real.log (499771 / 500000) ∧
    -Real.log (499771 / 500000) ≤ (91621 / 200000000) := by
  have h := checkLog_sound (w := (229 / 999771)) (n := 12)
    (lo := (57263 / 125000000)) (hi := (91621 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499771) = 1/(499771 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11956 : Bounds (-91621 / 200000000) (-57263 / 125000000) (Real.log (499771 / 500000)) := by
  have h := reflection_log_11956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11957_neg : (53266233 / 250000000) ≤ -Real.log (200000 / 247493) ∧
    -Real.log (200000 / 247493) ≤ (213064933 / 1000000000) := by
  have h := checkLog_sound (w := (47493 / 447493)) (n := 12)
    (lo := (53266233 / 250000000)) (hi := (213064933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247493 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247493 / 200000) = 1/(200000 / 247493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11957 : Bounds (53266233 / 250000000) (213064933 / 1000000000) (Real.log (247493 / 200000)) := by
  have h := reflection_log_11957_neg
  have he : Real.log (247493 / 200000) = -Real.log (200000 / 247493) := by
    rw [show ((247493 / 200000) : ℝ) = ((200000 / 247493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11958_neg : (271106869 / 1000000000) ≤ -Real.log (152507 / 200000) ∧
    -Real.log (152507 / 200000) ≤ (27110687 / 100000000) := by
  have h := checkLog_sound (w := (47493 / 352507)) (n := 12)
    (lo := (271106869 / 1000000000)) (hi := (27110687 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152507) = 1/(152507 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11958 : Bounds (-27110687 / 100000000) (-271106869 / 1000000000) (Real.log (152507 / 200000)) := by
  have h := reflection_log_11958_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11959_neg : (53468581 / 250000000) ≤ -Real.log (1000000 / 1238467) ∧
    -Real.log (1000000 / 1238467) ≤ (8554973 / 40000000) := by
  have h := checkLog_sound (w := (238467 / 2238467)) (n := 12)
    (lo := (53468581 / 250000000)) (hi := (8554973 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238467 / 1000000) = 1/(1000000 / 1238467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11959 : Bounds (53468581 / 250000000) (8554973 / 40000000) (Real.log (1238467 / 1000000)) := by
  have h := reflection_log_11959_neg
  have he : Real.log (1238467 / 1000000) = -Real.log (1000000 / 1238467) := by
    rw [show ((1238467 / 1000000) : ℝ) = ((1000000 / 1238467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11960_neg : (68105443 / 250000000) ≤ -Real.log (761533 / 1000000) ∧
    -Real.log (761533 / 1000000) ≤ (272421773 / 1000000000) := by
  have h := checkLog_sound (w := (238467 / 1761533)) (n := 12)
    (lo := (68105443 / 250000000)) (hi := (272421773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761533) = 1/(761533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11960 : Bounds (-272421773 / 1000000000) (-68105443 / 250000000) (Real.log (761533 / 1000000)) := by
  have h := reflection_log_11960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11961_neg : (58547447 / 1000000000) ≤ -Real.log (943133489911 / 1000000000000) ∧
    -Real.log (943133489911 / 1000000000000) ≤ (7318431 / 125000000) := by
  have h := checkLog_sound (w := (56866510089 / 1943133489911)) (n := 12)
    (lo := (58547447 / 1000000000)) (hi := (7318431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 943133489911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 943133489911) = 1/(943133489911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11961 : Bounds (-7318431 / 125000000) (-58547447 / 1000000000) (Real.log (943133489911 / 1000000000000)) := by
  have h := reflection_log_11961_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11962_neg : (58041937 / 1000000000) ≤ -Real.log (37744414951 / 40000000000) ∧
    -Real.log (37744414951 / 40000000000) ≤ (29020969 / 500000000) := by
  have h := checkLog_sound (w := (2255585049 / 77744414951)) (n := 12)
    (lo := (58041937 / 1000000000)) (hi := (29020969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37744414951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37744414951) = 1/(37744414951 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11962 : Bounds (-29020969 / 500000000) (-58041937 / 1000000000) (Real.log (37744414951 / 40000000000)) := by
  have h := reflection_log_11962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11963_neg : (242085901 / 500000000) ≤ -Real.log (500000000000 / 811415213727) ∧
    -Real.log (500000000000 / 811415213727) ≤ (484171803 / 1000000000) := by
  have h := checkLog_sound (w := (311415213727 / 1311415213727)) (n := 12)
    (lo := (242085901 / 500000000)) (hi := (484171803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811415213727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811415213727 / 500000000000) = 1/(500000000000 / 811415213727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11963 : Bounds (242085901 / 500000000) (484171803 / 1000000000) (Real.log (811415213727 / 500000000000)) := by
  have h := reflection_log_11963_neg
  have he : Real.log (811415213727 / 500000000000) = -Real.log (500000000000 / 811415213727) := by
    rw [show ((811415213727 / 500000000000) : ℝ) = ((500000000000 / 811415213727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11964_neg : (15196753 / 31250000) ≤ -Real.log (250000000000 / 406570365303) ∧
    -Real.log (250000000000 / 406570365303) ≤ (486296097 / 1000000000) := by
  have h := checkLog_sound (w := (156570365303 / 656570365303)) (n := 12)
    (lo := (15196753 / 31250000)) (hi := (486296097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406570365303 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406570365303 / 250000000000) = 1/(250000000000 / 406570365303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11964 : Bounds (15196753 / 31250000) (486296097 / 1000000000) (Real.log (406570365303 / 250000000000)) := by
  have h := reflection_log_11964_neg
  have he : Real.log (406570365303 / 250000000000) = -Real.log (250000000000 / 406570365303) := by
    rw [show ((406570365303 / 250000000000) : ℝ) = ((250000000000 / 406570365303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11965_neg : (197405097 / 200000000) ≤ -Real.log (500000000000 / 1341620626151) ∧
    -Real.log (500000000000 / 1341620626151) ≤ (987025487 / 1000000000) := by
  have h := checkLog_sound (w := (341620626151 / 2341620626151)) (n := 12)
    (lo := (58775661 / 200000000)) (hi := (146939153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341620626151 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1341620626151 / 1000000000000) = 1/(500000000000 / 1341620626151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11965 : Bounds (197405097 / 200000000) (987025487 / 1000000000) (Real.log (1341620626151 / 500000000000)) := by
  have h := reflection_log_11965_neg
  have he : Real.log (1341620626151 / 500000000000) = -Real.log (500000000000 / 1341620626151) := by
    rw [show ((1341620626151 / 500000000000) : ℝ) = ((500000000000 / 1341620626151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11966_neg : (98955491 / 100000000) ≤ -Real.log (100000000000 / 269003690037) ∧
    -Real.log (100000000000 / 269003690037) ≤ (30923591 / 31250000) := by
  have h := checkLog_sound (w := (69003690037 / 469003690037)) (n := 12)
    (lo := (29640773 / 100000000)) (hi := (296407731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269003690037 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269003690037 / 200000000000) = 1/(100000000000 / 269003690037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11966 : Bounds (98955491 / 100000000) (30923591 / 31250000) (Real.log (269003690037 / 100000000000)) := by
  have h := reflection_log_11966_neg
  have he : Real.log (269003690037 / 100000000000) = -Real.log (100000000000 / 269003690037) := by
    rw [show ((269003690037 / 100000000000) : ℝ) = ((100000000000 / 269003690037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11967_neg : (377751269 / 1000000000) ≤ -Real.log (1000 / 1459) ∧
    -Real.log (1000 / 1459) ≤ (37775127 / 100000000) := by
  have h := checkLog_sound (w := (459 / 2459)) (n := 12)
    (lo := (377751269 / 1000000000)) (hi := (37775127 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1459 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1459 / 1000) = 1/(1000 / 1459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11967 : Bounds (377751269 / 1000000000) (37775127 / 100000000) (Real.log (1459 / 1000)) := by
  have h := reflection_log_11967_neg
  have he : Real.log (1459 / 1000) = -Real.log (1000 / 1459) := by
    rw [show ((1459 / 1000) : ℝ) = ((1000 / 1459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

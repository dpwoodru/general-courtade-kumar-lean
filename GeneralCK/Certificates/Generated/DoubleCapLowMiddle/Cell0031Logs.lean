import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0031
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (340422629 / 500000000) ≤ -Real.log (12800 / 25287) ∧
    -Real.log (12800 / 25287) ≤ (680845259 / 1000000000) := by
  have h := checkLog_sound (w := (12487 / 38087)) (n := 12)
    (lo := (340422629 / 500000000)) (hi := (680845259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25287 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25287 / 12800) = 1/(12800 / 25287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (340422629 / 500000000) (680845259 / 1000000000) (Real.log (25287 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25287 / 12800) = -Real.log (12800 / 25287) := by
    rw [show ((25287 / 12800) : ℝ) = ((12800 / 25287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (463874657 / 125000000) ≤ -Real.log (313 / 12800) ∧
    -Real.log (313 / 12800) ≤ (1855498631 / 500000000) := by
  have h := checkLog_sound (w := (87 / 713)) (n := 12)
    (lo := (61315339 / 250000000)) (hi := (245261357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 313) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 313) = 1/(313 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1855498631 / 500000000) (-463874657 / 125000000) (Real.log (313 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170187833 / 250000000) ≤ -Real.log (102400 / 202277) ∧
    -Real.log (102400 / 202277) ≤ (680751333 / 1000000000) := by
  have h := checkLog_sound (w := (99877 / 304677)) (n := 12)
    (lo := (170187833 / 250000000)) (hi := (680751333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202277 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202277 / 102400) = 1/(102400 / 202277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170187833 / 250000000) (680751333 / 1000000000) (Real.log (202277 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202277 / 102400) = -Real.log (102400 / 202277) := by
    rw [show ((202277 / 102400) : ℝ) = ((102400 / 202277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (92585951 / 25000000) ≤ -Real.log (2523 / 102400) ∧
    -Real.log (2523 / 102400) ≤ (1851719023 / 500000000) := by
  have h := checkLog_sound (w := (677 / 5723)) (n := 12)
    (lo := (11885107 / 50000000)) (hi := (237702141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2523) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2523) = 1/(2523 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1851719023 / 500000000) (-92585951 / 25000000) (Real.log (2523 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (20887191 / 31250000) ≤ -Real.log (6400 / 12487) ∧
    -Real.log (6400 / 12487) ≤ (668390113 / 1000000000) := by
  have h := checkLog_sound (w := (6087 / 18887)) (n := 12)
    (lo := (20887191 / 31250000)) (hi := (668390113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12487 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12487 / 6400) = 1/(6400 / 12487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (20887191 / 31250000) (668390113 / 1000000000) (Real.log (12487 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12487 / 6400) = -Real.log (6400 / 12487) := by
    rw [show ((12487 / 6400) : ℝ) = ((6400 / 12487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (754462519 / 250000000) ≤ -Real.log (313 / 6400) ∧
    -Real.log (313 / 6400) ≤ (3017850081 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 713)) (n := 12)
    (lo := (61315339 / 250000000)) (hi := (245261357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 313) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 313) = 1/(313 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3017850081 / 1000000000) (-754462519 / 250000000) (Real.log (313 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (83524987 / 125000000) ≤ -Real.log (51200 / 99877) ∧
    -Real.log (51200 / 99877) ≤ (668199897 / 1000000000) := by
  have h := checkLog_sound (w := (48677 / 151077)) (n := 12)
    (lo := (83524987 / 125000000)) (hi := (668199897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99877 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99877 / 51200) = 1/(51200 / 99877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (83524987 / 125000000) (668199897 / 1000000000) (Real.log (99877 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99877 / 51200) = -Real.log (51200 / 99877) := by
    rw [show ((99877 / 51200) : ℝ) = ((51200 / 99877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (150514543 / 50000000) ≤ -Real.log (2523 / 51200) ∧
    -Real.log (2523 / 51200) ≤ (602058173 / 200000000) := by
  have h := checkLog_sound (w := (677 / 5723)) (n := 12)
    (lo := (11885107 / 50000000)) (hi := (237702141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2523) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2523) = 1/(2523 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-602058173 / 200000000) (-150514543 / 50000000) (Real.log (2523 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (682701817 / 1000000000) ≤ -Real.log (500000 / 989609) ∧
    -Real.log (500000 / 989609) ≤ (341350909 / 500000000) := by
  have h := checkLog_sound (w := (489609 / 1489609)) (n := 12)
    (lo := (682701817 / 1000000000)) (hi := (341350909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989609 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989609 / 500000) = 1/(500000 / 989609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (682701817 / 1000000000) (341350909 / 500000000) (Real.log (989609 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (989609 / 500000) = -Real.log (500000 / 989609) := by
    rw [show ((989609 / 500000) : ℝ) = ((500000 / 989609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (242104253 / 62500000) ≤ -Real.log (10391 / 500000) ∧
    -Real.log (10391 / 500000) ≤ (1936834027 / 500000000) := by
  have h := checkLog_sound (w := (2617 / 13008)) (n := 12)
    (lo := (101983037 / 250000000)) (hi := (407932149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10391) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10391) = 1/(10391 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1936834027 / 500000000) (-242104253 / 62500000) (Real.log (10391 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (682778107 / 1000000000) ≤ -Real.log (1000000 / 1979369) ∧
    -Real.log (1000000 / 1979369) ≤ (170694527 / 250000000) := by
  have h := checkLog_sound (w := (979369 / 2979369)) (n := 12)
    (lo := (682778107 / 1000000000)) (hi := (170694527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979369 / 1000000) = 1/(1000000 / 1979369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (682778107 / 1000000000) (170694527 / 250000000) (Real.log (1979369 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1979369 / 1000000) = -Real.log (1000000 / 1979369) := by
    rw [show ((1979369 / 1000000) : ℝ) = ((1000000 / 1979369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3880960477 / 1000000000) ≤ -Real.log (20631 / 1000000) ∧
    -Real.log (20631 / 1000000) ≤ (3880960483 / 1000000000) := by
  have h := checkLog_sound (w := (10619 / 51881)) (n := 12)
    (lo := (415224577 / 1000000000)) (hi := (207612289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20631) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20631) = 1/(20631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3880960483 / 1000000000) (-3880960477 / 1000000000) (Real.log (20631 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682652301 / 1000000000) ≤ -Real.log (12500 / 24739) ∧
    -Real.log (12500 / 24739) ≤ (341326151 / 500000000) := by
  have h := checkLog_sound (w := (12239 / 37239)) (n := 12)
    (lo := (682652301 / 1000000000)) (hi := (341326151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24739 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24739 / 12500) = 1/(12500 / 24739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682652301 / 1000000000) (341326151 / 500000000) (Real.log (24739 / 12500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (24739 / 12500) = -Real.log (12500 / 24739) := by
    rw [show ((24739 / 12500) : ℝ) = ((12500 / 24739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3868963513 / 1000000000) ≤ -Real.log (261 / 12500) ∧
    -Real.log (261 / 12500) ≤ (3868963519 / 1000000000) := by
  have h := checkLog_sound (w := (1037 / 5213)) (n := 12)
    (lo := (403227613 / 1000000000)) (hi := (201613807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2088) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2088) = 1/(261 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3868963519 / 1000000000) (-3868963513 / 1000000000) (Real.log (261 / 12500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (6827291 / 10000000) ≤ -Real.log (125000 / 247409) ∧
    -Real.log (125000 / 247409) ≤ (682729101 / 1000000000) := by
  have h := checkLog_sound (w := (122409 / 372409)) (n := 12)
    (lo := (6827291 / 10000000)) (hi := (682729101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247409 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247409 / 125000) = 1/(125000 / 247409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6827291 / 10000000) (682729101 / 1000000000) (Real.log (247409 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (247409 / 125000) = -Real.log (125000 / 247409) := by
    rw [show ((247409 / 125000) : ℝ) = ((125000 / 247409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (484533729 / 125000000) ≤ -Real.log (2591 / 125000) ∧
    -Real.log (2591 / 125000) ≤ (1938134919 / 500000000) := by
  have h := checkLog_sound (w := (5261 / 25989)) (n := 12)
    (lo := (102633483 / 250000000)) (hi := (410533933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10364) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10364) = 1/(2591 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1938134919 / 500000000) (-484533729 / 125000000) (Real.log (2591 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (911273973 / 200000000) ≤ -Real.log (250000000000 / 23809282071023) ∧
    -Real.log (250000000000 / 23809282071023) ≤ (284773117 / 62500000) := by
  have h := checkLog_sound (w := (7809282071023 / 39809282071023)) (n := 12)
    (lo := (79497357 / 200000000)) (hi := (198743393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23809282071023 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(23809282071023 / 16000000000000) = 1/(250000000000 / 23809282071023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (911273973 / 200000000) (284773117 / 62500000) (Real.log (23809282071023 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (23809282071023 / 250000000000) = -Real.log (250000000000 / 23809282071023) := by
    rw [show ((23809282071023 / 250000000000) : ℝ) = ((250000000000 / 23809282071023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4563738583 / 1000000000) ≤ -Real.log (500000000000 / 47970747903641) ∧
    -Real.log (500000000000 / 47970747903641) ≤ (456373859 / 100000000) := by
  have h := checkLog_sound (w := (15970747903641 / 79970747903641)) (n := 12)
    (lo := (404855503 / 1000000000)) (hi := (25303469 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47970747903641 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47970747903641 / 32000000000000) = 1/(500000000000 / 47970747903641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4563738583 / 1000000000) (456373859 / 100000000) (Real.log (47970747903641 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (47970747903641 / 500000000000) = -Real.log (500000000000 / 47970747903641) := by
    rw [show ((47970747903641 / 500000000000) : ℝ) = ((500000000000 / 47970747903641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2275807907 / 500000000) ≤ -Real.log (500000000000 / 47392720306513) ∧
    -Real.log (500000000000 / 47392720306513) ≤ (4551615821 / 1000000000) := by
  have h := checkLog_sound (w := (15392720306513 / 79392720306513)) (n := 12)
    (lo := (196366367 / 500000000)) (hi := (78546547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47392720306513 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47392720306513 / 32000000000000) = 1/(500000000000 / 47392720306513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2275807907 / 500000000) (4551615821 / 1000000000) (Real.log (47392720306513 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (47392720306513 / 500000000000) = -Real.log (500000000000 / 47392720306513) := by
    rw [show ((47392720306513 / 500000000000) : ℝ) = ((500000000000 / 47392720306513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1139749733 / 250000000) ≤ -Real.log (500000000000 / 47743921265921) ∧
    -Real.log (500000000000 / 47743921265921) ≤ (4558998939 / 1000000000) := by
  have h := checkLog_sound (w := (15743921265921 / 79743921265921)) (n := 12)
    (lo := (100028963 / 250000000)) (hi := (400115853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47743921265921 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47743921265921 / 32000000000000) = 1/(500000000000 / 47743921265921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1139749733 / 250000000) (4558998939 / 1000000000) (Real.log (47743921265921 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (47743921265921 / 500000000000) = -Real.log (500000000000 / 47743921265921) := by
    rw [show ((47743921265921 / 500000000000) : ℝ) = ((500000000000 / 47743921265921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0031

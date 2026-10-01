import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1408_neg : (648401 / 100000000) ≤ -Real.log (993536965551 / 1000000000000) ∧
    -Real.log (993536965551 / 1000000000000) ≤ (6484011 / 1000000000) := by
  have h := checkLog_sound (w := (6463034449 / 1993536965551)) (n := 12)
    (lo := (648401 / 100000000)) (hi := (6484011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993536965551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993536965551) = 1/(993536965551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1408 : Bounds (-6484011 / 1000000000) (-648401 / 100000000) (Real.log (993536965551 / 1000000000000)) := by
  have h := reflection_log_1408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1409_neg : (161133737 / 1000000000) ≤ -Real.log (500000000000 / 587421039639) ∧
    -Real.log (500000000000 / 587421039639) ≤ (80566869 / 500000000) := by
  have h := checkLog_sound (w := (87421039639 / 1087421039639)) (n := 12)
    (lo := (161133737 / 1000000000)) (hi := (80566869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587421039639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587421039639 / 500000000000) = 1/(500000000000 / 587421039639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1409 : Bounds (161133737 / 1000000000) (80566869 / 500000000) (Real.log (587421039639 / 500000000000)) := by
  have h := reflection_log_1409_neg
  have he : Real.log (587421039639 / 500000000000) = -Real.log (500000000000 / 587421039639) := by
    rw [show ((587421039639 / 500000000000) : ℝ) = ((500000000000 / 587421039639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1410_neg : (161560503 / 1000000000) ≤ -Real.log (500000000000 / 587671784163) ∧
    -Real.log (500000000000 / 587671784163) ≤ (20195063 / 125000000) := by
  have h := checkLog_sound (w := (87671784163 / 1087671784163)) (n := 12)
    (lo := (161560503 / 1000000000)) (hi := (20195063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587671784163 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587671784163 / 500000000000) = 1/(500000000000 / 587671784163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1410 : Bounds (161560503 / 1000000000) (20195063 / 125000000) (Real.log (587671784163 / 500000000000)) := by
  have h := reflection_log_1410_neg
  have he : Real.log (587671784163 / 500000000000) = -Real.log (500000000000 / 587671784163) := by
    rw [show ((587671784163 / 500000000000) : ℝ) = ((500000000000 / 587671784163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1411_neg : (161591957 / 500000000) ≤ -Real.log (500000000000 / 690759704691) ∧
    -Real.log (500000000000 / 690759704691) ≤ (64636783 / 200000000) := by
  have h := checkLog_sound (w := (190759704691 / 1190759704691)) (n := 12)
    (lo := (161591957 / 500000000)) (hi := (64636783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690759704691 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690759704691 / 500000000000) = 1/(500000000000 / 690759704691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1411 : Bounds (161591957 / 500000000) (64636783 / 200000000) (Real.log (690759704691 / 500000000000)) := by
  have h := reflection_log_1411_neg
  have he : Real.log (690759704691 / 500000000000) = -Real.log (500000000000 / 690759704691) := by
    rw [show ((690759704691 / 500000000000) : ℝ) = ((500000000000 / 690759704691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1412_neg : (161694593 / 500000000) ≤ -Real.log (100000000000 / 138180302489) ∧
    -Real.log (100000000000 / 138180302489) ≤ (323389187 / 1000000000) := by
  have h := checkLog_sound (w := (38180302489 / 238180302489)) (n := 12)
    (lo := (161694593 / 500000000)) (hi := (323389187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138180302489 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138180302489 / 100000000000) = 1/(100000000000 / 138180302489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1412 : Bounds (161694593 / 500000000) (323389187 / 1000000000) (Real.log (138180302489 / 100000000000)) := by
  have h := reflection_log_1412_neg
  have he : Real.log (138180302489 / 100000000000) = -Real.log (100000000000 / 138180302489) := by
    rw [show ((138180302489 / 100000000000) : ℝ) = ((100000000000 / 138180302489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1413_neg : (148764773 / 1000000000) ≤ -Real.log (2500 / 2901) ∧
    -Real.log (2500 / 2901) ≤ (74382387 / 500000000) := by
  have h := checkLog_sound (w := (401 / 5401)) (n := 12)
    (lo := (148764773 / 1000000000)) (hi := (74382387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2901 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2901 / 2500) = 1/(2500 / 2901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1413 : Bounds (148764773 / 1000000000) (74382387 / 500000000) (Real.log (2901 / 2500)) := by
  have h := reflection_log_1413_neg
  have he : Real.log (2901 / 2500) = -Real.log (2500 / 2901) := by
    rw [show ((2901 / 2500) : ℝ) = ((2500 / 2901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1414_neg : (174829691 / 1000000000) ≤ -Real.log (2099 / 2500) ∧
    -Real.log (2099 / 2500) ≤ (43707423 / 250000000) := by
  have h := checkLog_sound (w := (401 / 4599)) (n := 12)
    (lo := (174829691 / 1000000000)) (hi := (43707423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2099) = 1/(2099 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1414 : Bounds (-43707423 / 250000000) (-174829691 / 1000000000) (Real.log (2099 / 2500)) := by
  have h := reflection_log_1414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1415_neg : (160387 / 1000000000) ≤ -Real.log (2500000 / 2500401) ∧
    -Real.log (2500000 / 2500401) ≤ (40097 / 250000000) := by
  have h := checkLog_sound (w := (401 / 5000401)) (n := 12)
    (lo := (160387 / 1000000000)) (hi := (40097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500401 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500401 / 2500000) = 1/(2500000 / 2500401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1415 : Bounds (160387 / 1000000000) (40097 / 250000000) (Real.log (2500401 / 2500000)) := by
  have h := reflection_log_1415_neg
  have he : Real.log (2500401 / 2500000) = -Real.log (2500000 / 2500401) := by
    rw [show ((2500401 / 2500000) : ℝ) = ((2500000 / 2500401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1416_neg : (40103 / 250000000) ≤ -Real.log (2499599 / 2500000) ∧
    -Real.log (2499599 / 2500000) ≤ (160413 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 4999599)) (n := 12)
    (lo := (40103 / 250000000)) (hi := (160413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499599) = 1/(2499599 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1416 : Bounds (-160413 / 1000000000) (-40103 / 250000000) (Real.log (2499599 / 2500000)) := by
  have h := reflection_log_1416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1417_neg : (77372067 / 1000000000) ≤ -Real.log (250000 / 270111) ∧
    -Real.log (250000 / 270111) ≤ (19343017 / 250000000) := by
  have h := checkLog_sound (w := (20111 / 520111)) (n := 12)
    (lo := (77372067 / 1000000000)) (hi := (19343017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270111 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270111 / 250000) = 1/(250000 / 270111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1417 : Bounds (77372067 / 1000000000) (19343017 / 250000000) (Real.log (270111 / 250000)) := by
  have h := reflection_log_1417_neg
  have he : Real.log (270111 / 250000) = -Real.log (250000 / 270111) := by
    rw [show ((270111 / 250000) : ℝ) = ((250000 / 270111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1418_neg : (41932167 / 500000000) ≤ -Real.log (229889 / 250000) ∧
    -Real.log (229889 / 250000) ≤ (16772867 / 200000000) := by
  have h := checkLog_sound (w := (20111 / 479889)) (n := 12)
    (lo := (41932167 / 500000000)) (hi := (16772867 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229889) = 1/(229889 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1418 : Bounds (-16772867 / 200000000) (-41932167 / 500000000) (Real.log (229889 / 250000)) := by
  have h := reflection_log_1418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1419_neg : (38783669 / 500000000) ≤ -Real.log (200000 / 216131) ∧
    -Real.log (200000 / 216131) ≤ (77567339 / 1000000000) := by
  have h := checkLog_sound (w := (16131 / 416131)) (n := 12)
    (lo := (38783669 / 500000000)) (hi := (77567339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216131 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216131 / 200000) = 1/(200000 / 216131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1419 : Bounds (38783669 / 500000000) (77567339 / 1000000000) (Real.log (216131 / 200000)) := by
  have h := reflection_log_1419_neg
  have he : Real.log (216131 / 200000) = -Real.log (200000 / 216131) := by
    rw [show ((216131 / 200000) : ℝ) = ((200000 / 216131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1420_neg : (84093819 / 1000000000) ≤ -Real.log (183869 / 200000) ∧
    -Real.log (183869 / 200000) ≤ (4204691 / 50000000) := by
  have h := checkLog_sound (w := (16131 / 383869)) (n := 12)
    (lo := (84093819 / 1000000000)) (hi := (4204691 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183869) = 1/(183869 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1420 : Bounds (-4204691 / 50000000) (-84093819 / 1000000000) (Real.log (183869 / 200000)) := by
  have h := reflection_log_1420_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1421_neg : (81581 / 12500000) ≤ -Real.log (39739790839 / 40000000000) ∧
    -Real.log (39739790839 / 40000000000) ≤ (6526481 / 1000000000) := by
  have h := checkLog_sound (w := (260209161 / 79739790839)) (n := 12)
    (lo := (81581 / 12500000)) (hi := (6526481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39739790839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39739790839) = 1/(39739790839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1421 : Bounds (-6526481 / 1000000000) (-81581 / 12500000) (Real.log (39739790839 / 40000000000)) := by
  have h := reflection_log_1421_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1422_neg : (3246133 / 500000000) ≤ -Real.log (62095547679 / 62500000000) ∧
    -Real.log (62095547679 / 62500000000) ≤ (6492267 / 1000000000) := by
  have h := checkLog_sound (w := (404452321 / 124595547679)) (n := 12)
    (lo := (3246133 / 500000000)) (hi := (6492267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62095547679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62095547679) = 1/(62095547679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1422 : Bounds (-6492267 / 1000000000) (-3246133 / 500000000) (Real.log (62095547679 / 62500000000)) := by
  have h := reflection_log_1422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1423_neg : (161236401 / 1000000000) ≤ -Real.log (250000000000 / 293740674847) ∧
    -Real.log (250000000000 / 293740674847) ≤ (80618201 / 500000000) := by
  have h := checkLog_sound (w := (43740674847 / 543740674847)) (n := 12)
    (lo := (161236401 / 1000000000)) (hi := (80618201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293740674847 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293740674847 / 250000000000) = 1/(250000000000 / 293740674847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1423 : Bounds (161236401 / 1000000000) (80618201 / 500000000) (Real.log (293740674847 / 250000000000)) := by
  have h := reflection_log_1423_neg
  have he : Real.log (293740674847 / 250000000000) = -Real.log (250000000000 / 293740674847) := by
    rw [show ((293740674847 / 250000000000) : ℝ) = ((250000000000 / 293740674847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1424_neg : (161661157 / 1000000000) ≤ -Real.log (4000000000 / 4701847511) ∧
    -Real.log (4000000000 / 4701847511) ≤ (80830579 / 500000000) := by
  have h := checkLog_sound (w := (701847511 / 8701847511)) (n := 12)
    (lo := (161661157 / 1000000000)) (hi := (80830579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4701847511 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4701847511 / 4000000000) = 1/(4000000000 / 4701847511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1424 : Bounds (161661157 / 1000000000) (80830579 / 500000000) (Real.log (4701847511 / 4000000000)) := by
  have h := reflection_log_1424_neg
  have he : Real.log (4701847511 / 4000000000) = -Real.log (4000000000 / 4701847511) := by
    rw [show ((4701847511 / 4000000000) : ℝ) = ((4000000000 / 4701847511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1425_neg : (161694593 / 500000000) ≤ -Real.log (125000000000 / 172725378111) ∧
    -Real.log (125000000000 / 172725378111) ≤ (323389187 / 1000000000) := by
  have h := checkLog_sound (w := (47725378111 / 297725378111)) (n := 12)
    (lo := (161694593 / 500000000)) (hi := (323389187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172725378111 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172725378111 / 125000000000) = 1/(125000000000 / 172725378111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1425 : Bounds (161694593 / 500000000) (323389187 / 1000000000) (Real.log (172725378111 / 125000000000)) := by
  have h := reflection_log_1425_neg
  have he : Real.log (172725378111 / 125000000000) = -Real.log (125000000000 / 172725378111) := by
    rw [show ((172725378111 / 125000000000) : ℝ) = ((125000000000 / 172725378111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1426_neg : (10112327 / 31250000) ≤ -Real.log (500000000000 / 691043353979) ∧
    -Real.log (500000000000 / 691043353979) ≤ (64718893 / 200000000) := by
  have h := checkLog_sound (w := (191043353979 / 1191043353979)) (n := 12)
    (lo := (10112327 / 31250000)) (hi := (64718893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691043353979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691043353979 / 500000000000) = 1/(500000000000 / 691043353979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1426 : Bounds (10112327 / 31250000) (64718893 / 200000000) (Real.log (691043353979 / 500000000000)) := by
  have h := reflection_log_1426_neg
  have he : Real.log (691043353979 / 500000000000) = -Real.log (500000000000 / 691043353979) := by
    rw [show ((691043353979 / 500000000000) : ℝ) = ((500000000000 / 691043353979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1427_neg : (74425473 / 500000000) ≤ -Real.log (2000 / 2321) ∧
    -Real.log (2000 / 2321) ≤ (148850947 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 4321)) (n := 12)
    (lo := (74425473 / 500000000)) (hi := (148850947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2321 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2321 / 2000) = 1/(2000 / 2321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1427 : Bounds (74425473 / 500000000) (148850947 / 1000000000) (Real.log (2321 / 2000)) := by
  have h := reflection_log_1427_neg
  have he : Real.log (2321 / 2000) = -Real.log (2000 / 2321) := by
    rw [show ((2321 / 2000) : ℝ) = ((2000 / 2321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1428_neg : (87474401 / 500000000) ≤ -Real.log (1679 / 2000) ∧
    -Real.log (1679 / 2000) ≤ (174948803 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 3679)) (n := 12)
    (lo := (87474401 / 500000000)) (hi := (174948803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1679) = 1/(1679 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1428 : Bounds (-174948803 / 1000000000) (-87474401 / 500000000) (Real.log (1679 / 2000)) := by
  have h := reflection_log_1428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1429_neg : (160487 / 1000000000) ≤ -Real.log (2000000 / 2000321) ∧
    -Real.log (2000000 / 2000321) ≤ (20061 / 125000000) := by
  have h := checkLog_sound (w := (321 / 4000321)) (n := 12)
    (lo := (160487 / 1000000000)) (hi := (20061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000321 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000321 / 2000000) = 1/(2000000 / 2000321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1429 : Bounds (160487 / 1000000000) (20061 / 125000000) (Real.log (2000321 / 2000000)) := by
  have h := reflection_log_1429_neg
  have he : Real.log (2000321 / 2000000) = -Real.log (2000000 / 2000321) := by
    rw [show ((2000321 / 2000000) : ℝ) = ((2000000 / 2000321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1430_neg : (627 / 3906250) ≤ -Real.log (1999679 / 2000000) ∧
    -Real.log (1999679 / 2000000) ≤ (160513 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 3999679)) (n := 12)
    (lo := (627 / 3906250)) (hi := (160513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999679) = 1/(1999679 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1430 : Bounds (-160513 / 1000000000) (-627 / 3906250) (Real.log (1999679 / 2000000)) := by
  have h := reflection_log_1430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1431_neg : (77419269 / 1000000000) ≤ -Real.log (200000 / 216099) ∧
    -Real.log (200000 / 216099) ≤ (7741927 / 100000000) := by
  have h := checkLog_sound (w := (16099 / 416099)) (n := 12)
    (lo := (77419269 / 1000000000)) (hi := (7741927 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216099 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216099 / 200000) = 1/(200000 / 216099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1431 : Bounds (77419269 / 1000000000) (7741927 / 100000000) (Real.log (216099 / 200000)) := by
  have h := reflection_log_1431_neg
  have he : Real.log (216099 / 200000) = -Real.log (200000 / 216099) := by
    rw [show ((216099 / 200000) : ℝ) = ((200000 / 216099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1432_neg : (83919797 / 1000000000) ≤ -Real.log (183901 / 200000) ∧
    -Real.log (183901 / 200000) ≤ (41959899 / 500000000) := by
  have h := checkLog_sound (w := (16099 / 383901)) (n := 12)
    (lo := (83919797 / 1000000000)) (hi := (41959899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183901) = 1/(183901 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1432 : Bounds (-41959899 / 500000000) (-83919797 / 1000000000) (Real.log (183901 / 200000)) := by
  have h := reflection_log_1432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1433_neg : (77614531 / 1000000000) ≤ -Real.log (500000 / 540353) ∧
    -Real.log (500000 / 540353) ≤ (19403633 / 250000000) := by
  have h := checkLog_sound (w := (40353 / 1040353)) (n := 12)
    (lo := (77614531 / 1000000000)) (hi := (19403633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540353 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540353 / 500000) = 1/(500000 / 540353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1433 : Bounds (77614531 / 1000000000) (19403633 / 250000000) (Real.log (540353 / 500000)) := by
  have h := reflection_log_1433_neg
  have he : Real.log (540353 / 500000) = -Real.log (500000 / 540353) := by
    rw [show ((540353 / 500000) : ℝ) = ((500000 / 540353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1434_neg : (42074647 / 500000000) ≤ -Real.log (459647 / 500000) ∧
    -Real.log (459647 / 500000) ≤ (16829859 / 200000000) := by
  have h := checkLog_sound (w := (40353 / 959647)) (n := 12)
    (lo := (42074647 / 500000000)) (hi := (16829859 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459647) = 1/(459647 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1434 : Bounds (-16829859 / 200000000) (-42074647 / 500000000) (Real.log (459647 / 500000)) := by
  have h := reflection_log_1434_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1435_neg : (6534763 / 1000000000) ≤ -Real.log (248371635391 / 250000000000) ∧
    -Real.log (248371635391 / 250000000000) ≤ (1633691 / 250000000) := by
  have h := checkLog_sound (w := (1628364609 / 498371635391)) (n := 12)
    (lo := (6534763 / 1000000000)) (hi := (1633691 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248371635391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248371635391) = 1/(248371635391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1435 : Bounds (-1633691 / 250000000) (-6534763 / 1000000000) (Real.log (248371635391 / 250000000000)) := by
  have h := reflection_log_1435_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1436_neg : (6500527 / 1000000000) ≤ -Real.log (39740822199 / 40000000000) ∧
    -Real.log (39740822199 / 40000000000) ≤ (406283 / 62500000) := by
  have h := checkLog_sound (w := (259177801 / 79740822199)) (n := 12)
    (lo := (6500527 / 1000000000)) (hi := (406283 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39740822199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39740822199) = 1/(39740822199 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1436 : Bounds (-406283 / 62500000) (-6500527 / 1000000000) (Real.log (39740822199 / 40000000000)) := by
  have h := reflection_log_1436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1437_neg : (80669533 / 500000000) ≤ -Real.log (12500000000 / 14688541661) ∧
    -Real.log (12500000000 / 14688541661) ≤ (161339067 / 1000000000) := by
  have h := checkLog_sound (w := (2188541661 / 27188541661)) (n := 12)
    (lo := (80669533 / 500000000)) (hi := (161339067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14688541661 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14688541661 / 12500000000) = 1/(12500000000 / 14688541661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1437 : Bounds (80669533 / 500000000) (161339067 / 1000000000) (Real.log (14688541661 / 12500000000)) := by
  have h := reflection_log_1437_neg
  have he : Real.log (14688541661 / 12500000000) = -Real.log (12500000000 / 14688541661) := by
    rw [show ((14688541661 / 12500000000) : ℝ) = ((12500000000 / 14688541661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1438_neg : (80881913 / 500000000) ≤ -Real.log (500000000000 / 587791283311) ∧
    -Real.log (500000000000 / 587791283311) ≤ (161763827 / 1000000000) := by
  have h := checkLog_sound (w := (87791283311 / 1087791283311)) (n := 12)
    (lo := (80881913 / 500000000)) (hi := (161763827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587791283311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587791283311 / 500000000000) = 1/(500000000000 / 587791283311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1438 : Bounds (80881913 / 500000000) (161763827 / 1000000000) (Real.log (587791283311 / 500000000000)) := by
  have h := reflection_log_1438_neg
  have he : Real.log (587791283311 / 500000000000) = -Real.log (500000000000 / 587791283311) := by
    rw [show ((587791283311 / 500000000000) : ℝ) = ((500000000000 / 587791283311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1439_neg : (10112327 / 31250000) ≤ -Real.log (250000000000 / 345521676989) ∧
    -Real.log (250000000000 / 345521676989) ≤ (64718893 / 200000000) := by
  have h := checkLog_sound (w := (95521676989 / 595521676989)) (n := 12)
    (lo := (10112327 / 31250000)) (hi := (64718893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345521676989 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345521676989 / 250000000000) = 1/(250000000000 / 345521676989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1439 : Bounds (10112327 / 31250000) (64718893 / 200000000) (Real.log (345521676989 / 250000000000)) := by
  have h := reflection_log_1439_neg
  have he : Real.log (345521676989 / 250000000000) = -Real.log (250000000000 / 345521676989) := by
    rw [show ((345521676989 / 250000000000) : ℝ) = ((250000000000 / 345521676989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1440_neg : (323799749 / 1000000000) ≤ -Real.log (62500000000 / 86398153663) ∧
    -Real.log (62500000000 / 86398153663) ≤ (1295199 / 4000000) := by
  have h := checkLog_sound (w := (23898153663 / 148898153663)) (n := 12)
    (lo := (323799749 / 1000000000)) (hi := (1295199 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86398153663 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86398153663 / 62500000000) = 1/(62500000000 / 86398153663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1440 : Bounds (323799749 / 1000000000) (1295199 / 4000000) (Real.log (86398153663 / 62500000000)) := by
  have h := reflection_log_1440_neg
  have he : Real.log (86398153663 / 62500000000) = -Real.log (62500000000 / 86398153663) := by
    rw [show ((86398153663 / 62500000000) : ℝ) = ((62500000000 / 86398153663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1441_neg : (18617139 / 125000000) ≤ -Real.log (5000 / 5803) ∧
    -Real.log (5000 / 5803) ≤ (148937113 / 1000000000) := by
  have h := checkLog_sound (w := (803 / 10803)) (n := 12)
    (lo := (18617139 / 125000000)) (hi := (148937113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5803 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5803 / 5000) = 1/(5000 / 5803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1441 : Bounds (18617139 / 125000000) (148937113 / 1000000000) (Real.log (5803 / 5000)) := by
  have h := reflection_log_1441_neg
  have he : Real.log (5803 / 5000) = -Real.log (5000 / 5803) := by
    rw [show ((5803 / 5000) : ℝ) = ((5000 / 5803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1442_neg : (21883491 / 125000000) ≤ -Real.log (4197 / 5000) ∧
    -Real.log (4197 / 5000) ≤ (175067929 / 1000000000) := by
  have h := checkLog_sound (w := (803 / 9197)) (n := 12)
    (lo := (21883491 / 125000000)) (hi := (175067929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4197) = 1/(4197 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1442 : Bounds (-175067929 / 1000000000) (-21883491 / 125000000) (Real.log (4197 / 5000)) := by
  have h := reflection_log_1442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1443_neg : (160587 / 1000000000) ≤ -Real.log (5000000 / 5000803) ∧
    -Real.log (5000000 / 5000803) ≤ (40147 / 250000000) := by
  have h := checkLog_sound (w := (803 / 10000803)) (n := 12)
    (lo := (160587 / 1000000000)) (hi := (40147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000803 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000803 / 5000000) = 1/(5000000 / 5000803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1443 : Bounds (160587 / 1000000000) (40147 / 250000000) (Real.log (5000803 / 5000000)) := by
  have h := reflection_log_1443_neg
  have he : Real.log (5000803 / 5000000) = -Real.log (5000000 / 5000803) := by
    rw [show ((5000803 / 5000000) : ℝ) = ((5000000 / 5000803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1444_neg : (40153 / 250000000) ≤ -Real.log (4999197 / 5000000) ∧
    -Real.log (4999197 / 5000000) ≤ (160613 / 1000000000) := by
  have h := checkLog_sound (w := (803 / 9999197)) (n := 12)
    (lo := (40153 / 250000000)) (hi := (160613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999197) = 1/(4999197 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1444 : Bounds (-160613 / 1000000000) (-40153 / 250000000) (Real.log (4999197 / 5000000)) := by
  have h := reflection_log_1444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1445_neg : (77465543 / 1000000000) ≤ -Real.log (200000 / 216109) ∧
    -Real.log (200000 / 216109) ≤ (9683193 / 125000000) := by
  have h := checkLog_sound (w := (16109 / 416109)) (n := 12)
    (lo := (77465543 / 1000000000)) (hi := (9683193 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216109 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216109 / 200000) = 1/(200000 / 216109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1445 : Bounds (77465543 / 1000000000) (9683193 / 125000000) (Real.log (216109 / 200000)) := by
  have h := reflection_log_1445_neg
  have he : Real.log (216109 / 200000) = -Real.log (200000 / 216109) := by
    rw [show ((216109 / 200000) : ℝ) = ((200000 / 216109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1446_neg : (3358967 / 40000000) ≤ -Real.log (183891 / 200000) ∧
    -Real.log (183891 / 200000) ≤ (2624193 / 31250000) := by
  have h := checkLog_sound (w := (16109 / 383891)) (n := 12)
    (lo := (3358967 / 40000000)) (hi := (2624193 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183891) = 1/(183891 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1446 : Bounds (-2624193 / 31250000) (-3358967 / 40000000) (Real.log (183891 / 200000)) := by
  have h := reflection_log_1446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1447_neg : (77661721 / 1000000000) ≤ -Real.log (1000000 / 1080757) ∧
    -Real.log (1000000 / 1080757) ≤ (38830861 / 500000000) := by
  have h := checkLog_sound (w := (80757 / 2080757)) (n := 12)
    (lo := (77661721 / 1000000000)) (hi := (38830861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080757 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080757 / 1000000) = 1/(1000000 / 1080757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1447 : Bounds (77661721 / 1000000000) (38830861 / 500000000) (Real.log (1080757 / 1000000)) := by
  have h := reflection_log_1447_neg
  have he : Real.log (1080757 / 1000000) = -Real.log (1000000 / 1080757) := by
    rw [show ((1080757 / 1000000) : ℝ) = ((1000000 / 1080757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1448_neg : (84204773 / 1000000000) ≤ -Real.log (919243 / 1000000) ∧
    -Real.log (919243 / 1000000) ≤ (42102387 / 500000000) := by
  have h := checkLog_sound (w := (80757 / 1919243)) (n := 12)
    (lo := (84204773 / 1000000000)) (hi := (42102387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919243) = 1/(919243 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1448 : Bounds (-42102387 / 500000000) (-84204773 / 1000000000) (Real.log (919243 / 1000000)) := by
  have h := reflection_log_1448_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1449_neg : (1635763 / 250000000) ≤ -Real.log (993478306951 / 1000000000000) ∧
    -Real.log (993478306951 / 1000000000000) ≤ (6543053 / 1000000000) := by
  have h := checkLog_sound (w := (6521693049 / 1993478306951)) (n := 12)
    (lo := (1635763 / 250000000)) (hi := (6543053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993478306951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993478306951) = 1/(993478306951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1449 : Bounds (-6543053 / 1000000000) (-1635763 / 250000000) (Real.log (993478306951 / 1000000000000)) := by
  have h := reflection_log_1449_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1450_neg : (813579 / 125000000) ≤ -Real.log (39740500119 / 40000000000) ∧
    -Real.log (39740500119 / 40000000000) ≤ (6508633 / 1000000000) := by
  have h := checkLog_sound (w := (259499881 / 79740500119)) (n := 12)
    (lo := (813579 / 125000000)) (hi := (6508633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39740500119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39740500119) = 1/(39740500119 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1450 : Bounds (-6508633 / 1000000000) (-813579 / 125000000) (Real.log (39740500119 / 40000000000)) := by
  have h := reflection_log_1450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1451_neg : (161439719 / 1000000000) ≤ -Real.log (500000000000 / 587600806999) ∧
    -Real.log (500000000000 / 587600806999) ≤ (4035993 / 25000000) := by
  have h := checkLog_sound (w := (87600806999 / 1087600806999)) (n := 12)
    (lo := (161439719 / 1000000000)) (hi := (4035993 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587600806999 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587600806999 / 500000000000) = 1/(500000000000 / 587600806999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1451 : Bounds (161439719 / 1000000000) (4035993 / 25000000) (Real.log (587600806999 / 500000000000)) := by
  have h := reflection_log_1451_neg
  have he : Real.log (587600806999 / 500000000000) = -Real.log (500000000000 / 587600806999) := by
    rw [show ((587600806999 / 500000000000) : ℝ) = ((500000000000 / 587600806999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1452_neg : (32373299 / 200000000) ≤ -Real.log (500000000000 / 587851634443) ∧
    -Real.log (500000000000 / 587851634443) ≤ (632291 / 3906250) := by
  have h := checkLog_sound (w := (87851634443 / 1087851634443)) (n := 12)
    (lo := (32373299 / 200000000)) (hi := (632291 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587851634443 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587851634443 / 500000000000) = 1/(500000000000 / 587851634443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1452 : Bounds (32373299 / 200000000) (632291 / 3906250) (Real.log (587851634443 / 500000000000)) := by
  have h := reflection_log_1452_neg
  have he : Real.log (587851634443 / 500000000000) = -Real.log (500000000000 / 587851634443) := by
    rw [show ((587851634443 / 500000000000) : ℝ) = ((500000000000 / 587851634443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1453_neg : (323799749 / 1000000000) ≤ -Real.log (500000000000 / 691185229303) ∧
    -Real.log (500000000000 / 691185229303) ≤ (1295199 / 4000000) := by
  have h := checkLog_sound (w := (191185229303 / 1191185229303)) (n := 12)
    (lo := (323799749 / 1000000000)) (hi := (1295199 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691185229303 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691185229303 / 500000000000) = 1/(500000000000 / 691185229303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1453 : Bounds (323799749 / 1000000000) (1295199 / 4000000) (Real.log (691185229303 / 500000000000)) := by
  have h := reflection_log_1453_neg
  have he : Real.log (691185229303 / 500000000000) = -Real.log (500000000000 / 691185229303) := by
    rw [show ((691185229303 / 500000000000) : ℝ) = ((500000000000 / 691185229303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1454_neg : (4050063 / 12500000) ≤ -Real.log (500000000000 / 691327138433) ∧
    -Real.log (500000000000 / 691327138433) ≤ (324005041 / 1000000000) := by
  have h := checkLog_sound (w := (191327138433 / 1191327138433)) (n := 12)
    (lo := (4050063 / 12500000)) (hi := (324005041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691327138433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691327138433 / 500000000000) = 1/(500000000000 / 691327138433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1454 : Bounds (4050063 / 12500000) (324005041 / 1000000000) (Real.log (691327138433 / 500000000000)) := by
  have h := reflection_log_1454_neg
  have he : Real.log (691327138433 / 500000000000) = -Real.log (500000000000 / 691327138433) := by
    rw [show ((691327138433 / 500000000000) : ℝ) = ((500000000000 / 691327138433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1455_neg : (149023271 / 1000000000) ≤ -Real.log (10000 / 11607) ∧
    -Real.log (10000 / 11607) ≤ (18627909 / 125000000) := by
  have h := checkLog_sound (w := (1607 / 21607)) (n := 12)
    (lo := (149023271 / 1000000000)) (hi := (18627909 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11607 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11607 / 10000) = 1/(10000 / 11607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1455 : Bounds (149023271 / 1000000000) (18627909 / 125000000) (Real.log (11607 / 10000)) := by
  have h := reflection_log_1455_neg
  have he : Real.log (11607 / 10000) = -Real.log (10000 / 11607) := by
    rw [show ((11607 / 10000) : ℝ) = ((10000 / 11607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1456_neg : (175187067 / 1000000000) ≤ -Real.log (8393 / 10000) ∧
    -Real.log (8393 / 10000) ≤ (43796767 / 250000000) := by
  have h := checkLog_sound (w := (1607 / 18393)) (n := 12)
    (lo := (175187067 / 1000000000)) (hi := (43796767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8393) = 1/(8393 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1456 : Bounds (-43796767 / 250000000) (-175187067 / 1000000000) (Real.log (8393 / 10000)) := by
  have h := reflection_log_1456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1457_neg : (160687 / 1000000000) ≤ -Real.log (10000000 / 10001607) ∧
    -Real.log (10000000 / 10001607) ≤ (10043 / 62500000) := by
  have h := checkLog_sound (w := (1607 / 20001607)) (n := 12)
    (lo := (160687 / 1000000000)) (hi := (10043 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001607 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001607 / 10000000) = 1/(10000000 / 10001607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1457 : Bounds (160687 / 1000000000) (10043 / 62500000) (Real.log (10001607 / 10000000)) := by
  have h := reflection_log_1457_neg
  have he : Real.log (10001607 / 10000000) = -Real.log (10000000 / 10001607) := by
    rw [show ((10001607 / 10000000) : ℝ) = ((10000000 / 10001607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1458_neg : (20089 / 125000000) ≤ -Real.log (9998393 / 10000000) ∧
    -Real.log (9998393 / 10000000) ≤ (160713 / 1000000000) := by
  have h := checkLog_sound (w := (1607 / 19998393)) (n := 12)
    (lo := (20089 / 125000000)) (hi := (160713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998393) = 1/(9998393 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1458 : Bounds (-160713 / 1000000000) (-20089 / 125000000) (Real.log (9998393 / 10000000)) := by
  have h := reflection_log_1458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1459_neg : (3875637 / 50000000) ≤ -Real.log (250000 / 270149) ∧
    -Real.log (250000 / 270149) ≤ (77512741 / 1000000000) := by
  have h := checkLog_sound (w := (20149 / 520149)) (n := 12)
    (lo := (3875637 / 50000000)) (hi := (77512741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270149 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270149 / 250000) = 1/(250000 / 270149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1459 : Bounds (3875637 / 50000000) (77512741 / 1000000000) (Real.log (270149 / 250000)) := by
  have h := reflection_log_1459_neg
  have he : Real.log (270149 / 250000) = -Real.log (250000 / 270149) := by
    rw [show ((270149 / 250000) : ℝ) = ((250000 / 270149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1460_neg : (21007411 / 250000000) ≤ -Real.log (229851 / 250000) ∧
    -Real.log (229851 / 250000) ≤ (16805929 / 200000000) := by
  have h := checkLog_sound (w := (20149 / 479851)) (n := 12)
    (lo := (21007411 / 250000000)) (hi := (16805929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229851) = 1/(229851 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1460 : Bounds (-16805929 / 200000000) (-21007411 / 250000000) (Real.log (229851 / 250000)) := by
  have h := reflection_log_1460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1461_neg : (77708909 / 1000000000) ≤ -Real.log (125000 / 135101) ∧
    -Real.log (125000 / 135101) ≤ (7770891 / 100000000) := by
  have h := checkLog_sound (w := (10101 / 260101)) (n := 12)
    (lo := (77708909 / 1000000000)) (hi := (7770891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135101 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135101 / 125000) = 1/(125000 / 135101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1461 : Bounds (77708909 / 1000000000) (7770891 / 100000000) (Real.log (135101 / 125000)) := by
  have h := reflection_log_1461_neg
  have he : Real.log (135101 / 125000) = -Real.log (125000 / 135101) := by
    rw [show ((135101 / 125000) : ℝ) = ((125000 / 135101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1462_neg : (16852051 / 200000000) ≤ -Real.log (114899 / 125000) ∧
    -Real.log (114899 / 125000) ≤ (2633133 / 31250000) := by
  have h := checkLog_sound (w := (10101 / 239899)) (n := 12)
    (lo := (16852051 / 200000000)) (hi := (2633133 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114899) = 1/(114899 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1462 : Bounds (-2633133 / 31250000) (-16852051 / 200000000) (Real.log (114899 / 125000)) := by
  have h := reflection_log_1462_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1463_neg : (3275673 / 500000000) ≤ -Real.log (15522969799 / 15625000000) ∧
    -Real.log (15522969799 / 15625000000) ≤ (6551347 / 1000000000) := by
  have h := checkLog_sound (w := (102030201 / 31147969799)) (n := 12)
    (lo := (3275673 / 500000000)) (hi := (6551347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15522969799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15522969799) = 1/(15522969799 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1463 : Bounds (-6551347 / 1000000000) (-3275673 / 500000000) (Real.log (15522969799 / 15625000000)) := by
  have h := reflection_log_1463_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1464_neg : (814613 / 125000000) ≤ -Real.log (62094017799 / 62500000000) ∧
    -Real.log (62094017799 / 62500000000) ≤ (1303381 / 200000000) := by
  have h := checkLog_sound (w := (405982201 / 124594017799)) (n := 12)
    (lo := (814613 / 125000000)) (hi := (1303381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62094017799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62094017799) = 1/(62094017799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1464 : Bounds (-1303381 / 200000000) (-814613 / 125000000) (Real.log (62094017799 / 62500000000)) := by
  have h := reflection_log_1464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1465_neg : (32308477 / 200000000) ≤ -Real.log (500000000000 / 587661136997) ∧
    -Real.log (500000000000 / 587661136997) ≤ (80771193 / 500000000) := by
  have h := checkLog_sound (w := (87661136997 / 1087661136997)) (n := 12)
    (lo := (32308477 / 200000000)) (hi := (80771193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587661136997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587661136997 / 500000000000) = 1/(500000000000 / 587661136997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1465 : Bounds (32308477 / 200000000) (80771193 / 500000000) (Real.log (587661136997 / 500000000000)) := by
  have h := reflection_log_1465_neg
  have he : Real.log (587661136997 / 500000000000) = -Real.log (500000000000 / 587661136997) := by
    rw [show ((587661136997 / 500000000000) : ℝ) = ((500000000000 / 587661136997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1466_neg : (32393833 / 200000000) ≤ -Real.log (31250000000 / 36744499517) ∧
    -Real.log (31250000000 / 36744499517) ≤ (80984583 / 500000000) := by
  have h := checkLog_sound (w := (5494499517 / 67994499517)) (n := 12)
    (lo := (32393833 / 200000000)) (hi := (80984583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36744499517 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36744499517 / 31250000000) = 1/(31250000000 / 36744499517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1466 : Bounds (32393833 / 200000000) (80984583 / 500000000) (Real.log (36744499517 / 31250000000)) := by
  have h := reflection_log_1466_neg
  have he : Real.log (36744499517 / 31250000000) = -Real.log (31250000000 / 36744499517) := by
    rw [show ((36744499517 / 31250000000) : ℝ) = ((31250000000 / 36744499517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1467_neg : (4050063 / 12500000) ≤ -Real.log (3906250000 / 5400993269) ∧
    -Real.log (3906250000 / 5400993269) ≤ (324005041 / 1000000000) := by
  have h := checkLog_sound (w := (1494743269 / 9307243269)) (n := 12)
    (lo := (4050063 / 12500000)) (hi := (324005041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5400993269 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5400993269 / 3906250000) = 1/(3906250000 / 5400993269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1467 : Bounds (4050063 / 12500000) (324005041 / 1000000000) (Real.log (5400993269 / 3906250000)) := by
  have h := reflection_log_1467_neg
  have he : Real.log (5400993269 / 3906250000) = -Real.log (3906250000 / 5400993269) := by
    rw [show ((5400993269 / 3906250000) : ℝ) = ((3906250000 / 5400993269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1468_neg : (324210339 / 1000000000) ≤ -Real.log (250000000000 / 345734540689) ∧
    -Real.log (250000000000 / 345734540689) ≤ (16210517 / 50000000) := by
  have h := checkLog_sound (w := (95734540689 / 595734540689)) (n := 12)
    (lo := (324210339 / 1000000000)) (hi := (16210517 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345734540689 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345734540689 / 250000000000) = 1/(250000000000 / 345734540689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1468 : Bounds (324210339 / 1000000000) (16210517 / 50000000) (Real.log (345734540689 / 250000000000)) := by
  have h := reflection_log_1468_neg
  have he : Real.log (345734540689 / 250000000000) = -Real.log (250000000000 / 345734540689) := by
    rw [show ((345734540689 / 250000000000) : ℝ) = ((250000000000 / 345734540689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1469_neg : (74554711 / 500000000) ≤ -Real.log (1250 / 1451) ∧
    -Real.log (1250 / 1451) ≤ (149109423 / 1000000000) := by
  have h := checkLog_sound (w := (201 / 2701)) (n := 12)
    (lo := (74554711 / 500000000)) (hi := (149109423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 1250) = 1/(1250 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1469 : Bounds (74554711 / 500000000) (149109423 / 1000000000) (Real.log (1451 / 1250)) := by
  have h := reflection_log_1469_neg
  have he : Real.log (1451 / 1250) = -Real.log (1250 / 1451) := by
    rw [show ((1451 / 1250) : ℝ) = ((1250 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1470_neg : (175306221 / 1000000000) ≤ -Real.log (1049 / 1250) ∧
    -Real.log (1049 / 1250) ≤ (87653111 / 500000000) := by
  have h := checkLog_sound (w := (201 / 2299)) (n := 12)
    (lo := (175306221 / 1000000000)) (hi := (87653111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1049) = 1/(1049 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1470 : Bounds (-87653111 / 500000000) (-175306221 / 1000000000) (Real.log (1049 / 1250)) := by
  have h := reflection_log_1470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1471_neg : (160787 / 1000000000) ≤ -Real.log (1250000 / 1250201) ∧
    -Real.log (1250000 / 1250201) ≤ (40197 / 250000000) := by
  have h := checkLog_sound (w := (201 / 2500201)) (n := 12)
    (lo := (160787 / 1000000000)) (hi := (40197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250201 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250201 / 1250000) = 1/(1250000 / 1250201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1471 : Bounds (160787 / 1000000000) (40197 / 250000000) (Real.log (1250201 / 1250000)) := by
  have h := reflection_log_1471_neg
  have he : Real.log (1250201 / 1250000) = -Real.log (1250000 / 1250201) := by
    rw [show ((1250201 / 1250000) : ℝ) = ((1250000 / 1250201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

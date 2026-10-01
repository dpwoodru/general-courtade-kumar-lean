import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0180
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

theorem reflection_log_1_neg : (626021983 / 1000000000) ≤ -Real.log (6400 / 11969) ∧
    -Real.log (6400 / 11969) ≤ (19563187 / 31250000) := by
  have h := checkLog_sound (w := (5569 / 18369)) (n := 12)
    (lo := (626021983 / 1000000000)) (hi := (19563187 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11969 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11969 / 6400) = 1/(6400 / 11969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (626021983 / 1000000000) (19563187 / 31250000) (Real.log (11969 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11969 / 6400) = -Real.log (6400 / 11969) := by
    rw [show ((11969 / 6400) : ℝ) = ((6400 / 11969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2041423473 / 1000000000) ≤ -Real.log (831 / 6400) ∧
    -Real.log (831 / 6400) ≤ (510355869 / 250000000) := by
  have h := checkLog_sound (w := (769 / 2431)) (n := 12)
    (lo := (655129113 / 1000000000)) (hi := (327564557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 831) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 831) = 1/(831 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-510355869 / 250000000) (-2041423473 / 1000000000) (Real.log (831 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (78054161 / 125000000) ≤ -Real.log (128 / 239) ∧
    -Real.log (128 / 239) ≤ (624433289 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 367)) (n := 12)
    (lo := (78054161 / 125000000)) (hi := (624433289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239 / 128) = 1/(128 / 239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (78054161 / 125000000) (624433289 / 1000000000) (Real.log (239 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (239 / 128) = -Real.log (128 / 239) := by
    rw [show ((239 / 128) : ℝ) = ((128 / 239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1009408459 / 500000000) ≤ -Real.log (17 / 128) ∧
    -Real.log (17 / 128) ≤ (2018816921 / 1000000000) := by
  have h := checkLog_sound (w := (15 / 49)) (n := 12)
    (lo := (316261279 / 500000000)) (hi := (632522559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 17) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 17) = 1/(17 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2018816921 / 1000000000) (-1009408459 / 500000000) (Real.log (17 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (277032347 / 500000000) ≤ -Real.log (3200 / 5569) ∧
    -Real.log (3200 / 5569) ≤ (110812939 / 200000000) := by
  have h := checkLog_sound (w := (2369 / 8769)) (n := 12)
    (lo := (277032347 / 500000000)) (hi := (110812939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5569 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5569 / 3200) = 1/(3200 / 5569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (277032347 / 500000000) (110812939 / 200000000) (Real.log (5569 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5569 / 3200) = -Real.log (3200 / 5569) := by
    rw [show ((5569 / 3200) : ℝ) = ((3200 / 5569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1348276293 / 1000000000) ≤ -Real.log (831 / 3200) ∧
    -Real.log (831 / 3200) ≤ (269655259 / 200000000) := by
  have h := checkLog_sound (w := (769 / 2431)) (n := 12)
    (lo := (655129113 / 1000000000)) (hi := (327564557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 831) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 831) = 1/(831 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-269655259 / 200000000) (-1348276293 / 1000000000) (Real.log (831 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (550647117 / 1000000000) ≤ -Real.log (64 / 111) ∧
    -Real.log (64 / 111) ≤ (275323559 / 500000000) := by
  have h := checkLog_sound (w := (47 / 175)) (n := 12)
    (lo := (550647117 / 1000000000)) (hi := (275323559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111 / 64) = 1/(64 / 111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (550647117 / 1000000000) (275323559 / 500000000) (Real.log (111 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (111 / 64) = -Real.log (64 / 111) := by
    rw [show ((111 / 64) : ℝ) = ((64 / 111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (662834869 / 500000000) ≤ -Real.log (17 / 64) ∧
    -Real.log (17 / 64) ≤ (66283487 / 50000000) := by
  have h := checkLog_sound (w := (15 / 49)) (n := 12)
    (lo := (316261279 / 500000000)) (hi := (632522559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 17) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 17) = 1/(17 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-66283487 / 50000000) (-662834869 / 500000000) (Real.log (17 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (128560687 / 200000000) ≤ -Real.log (200000 / 380361) ∧
    -Real.log (200000 / 380361) ≤ (160700859 / 250000000) := by
  have h := checkLog_sound (w := (180361 / 580361)) (n := 12)
    (lo := (128560687 / 200000000)) (hi := (160700859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380361 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380361 / 200000) = 1/(200000 / 380361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (128560687 / 200000000) (160700859 / 250000000) (Real.log (380361 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (380361 / 200000) = -Real.log (200000 / 380361) := by
    rw [show ((380361 / 200000) : ℝ) = ((200000 / 380361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2320799979 / 1000000000) ≤ -Real.log (19639 / 200000) ∧
    -Real.log (19639 / 200000) ≤ (2320799983 / 1000000000) := by
  have h := checkLog_sound (w := (5361 / 44639)) (n := 12)
    (lo := (241358439 / 1000000000)) (hi := (6033961 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19639) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 19639) = 1/(19639 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2320799983 / 1000000000) (-2320799979 / 1000000000) (Real.log (19639 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (321897579 / 500000000) ≤ -Real.log (250000 / 475923) ∧
    -Real.log (250000 / 475923) ≤ (643795159 / 1000000000) := by
  have h := checkLog_sound (w := (225923 / 725923)) (n := 12)
    (lo := (321897579 / 500000000)) (hi := (643795159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((475923 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(475923 / 250000) = 1/(250000 / 475923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (321897579 / 500000000) (643795159 / 1000000000) (Real.log (475923 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (475923 / 250000) = -Real.log (250000 / 475923) := by
    rw [show ((475923 / 250000) : ℝ) = ((250000 / 475923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (146262743 / 62500000) ≤ -Real.log (24077 / 250000) ∧
    -Real.log (24077 / 250000) ≤ (585050973 / 250000000) := by
  have h := checkLog_sound (w := (7173 / 55327)) (n := 12)
    (lo := (65190587 / 250000000)) (hi := (260762349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24077) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 24077) = 1/(24077 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-585050973 / 250000000) (-146262743 / 62500000) (Real.log (24077 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (25615017 / 40000000) ≤ -Real.log (1000000 / 1897193) ∧
    -Real.log (1000000 / 1897193) ≤ (320187713 / 500000000) := by
  have h := checkLog_sound (w := (897193 / 2897193)) (n := 12)
    (lo := (25615017 / 40000000)) (hi := (320187713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1897193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1897193 / 1000000) = 1/(1000000 / 1897193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (25615017 / 40000000) (320187713 / 500000000) (Real.log (1897193 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1897193 / 1000000) = -Real.log (1000000 / 1897193) := by
    rw [show ((1897193 / 1000000) : ℝ) = ((1000000 / 1897193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2274901833 / 1000000000) ≤ -Real.log (102807 / 1000000) ∧
    -Real.log (102807 / 1000000) ≤ (2274901837 / 1000000000) := by
  have h := checkLog_sound (w := (22193 / 227807)) (n := 12)
    (lo := (195460293 / 1000000000)) (hi := (97730147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102807) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 102807) = 1/(102807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2274901837 / 1000000000) (-2274901833 / 1000000000) (Real.log (102807 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (641496453 / 1000000000) ≤ -Real.log (1000000 / 1899321) ∧
    -Real.log (1000000 / 1899321) ≤ (320748227 / 500000000) := by
  have h := checkLog_sound (w := (899321 / 2899321)) (n := 12)
    (lo := (641496453 / 1000000000)) (hi := (320748227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899321 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899321 / 1000000) = 1/(1000000 / 1899321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (641496453 / 1000000000) (320748227 / 500000000) (Real.log (1899321 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1899321 / 1000000) = -Real.log (1000000 / 1899321) := by
    rw [show ((1899321 / 1000000) : ℝ) = ((1000000 / 1899321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2295818039 / 1000000000) ≤ -Real.log (100679 / 1000000) ∧
    -Real.log (100679 / 1000000) ≤ (2295818043 / 1000000000) := by
  have h := checkLog_sound (w := (24321 / 225679)) (n := 12)
    (lo := (216376499 / 1000000000)) (hi := (432753 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100679) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 100679) = 1/(100679 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2295818043 / 1000000000) (-2295818039 / 1000000000) (Real.log (100679 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1481801707 / 500000000) ≤ -Real.log (100000000000 / 1936763582667) ∧
    -Real.log (100000000000 / 1936763582667) ≤ (2963603419 / 1000000000) := by
  have h := checkLog_sound (w := (336763582667 / 3536763582667)) (n := 12)
    (lo := (95507347 / 500000000)) (hi := (38202939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1936763582667 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1936763582667 / 1600000000000) = 1/(100000000000 / 1936763582667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1481801707 / 500000000) (2963603419 / 1000000000) (Real.log (1936763582667 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1936763582667 / 100000000000) = -Real.log (100000000000 / 1936763582667) := by
    rw [show ((1936763582667 / 100000000000) : ℝ) = ((100000000000 / 1936763582667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1491999523 / 500000000) ≤ -Real.log (500000000000 / 9883353407817) ∧
    -Real.log (500000000000 / 9883353407817) ≤ (2983999051 / 1000000000) := by
  have h := checkLog_sound (w := (1883353407817 / 17883353407817)) (n := 12)
    (lo := (105705163 / 500000000)) (hi := (211410327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9883353407817 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9883353407817 / 8000000000000) = 1/(500000000000 / 9883353407817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1491999523 / 500000000) (2983999051 / 1000000000) (Real.log (9883353407817 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9883353407817 / 500000000000) = -Real.log (500000000000 / 9883353407817) := by
    rw [show ((9883353407817 / 500000000000) : ℝ) = ((500000000000 / 9883353407817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1457638629 / 500000000) ≤ -Real.log (500000000000 / 9226964117229) ∧
    -Real.log (500000000000 / 9226964117229) ≤ (2915277263 / 1000000000) := by
  have h := checkLog_sound (w := (1226964117229 / 17226964117229)) (n := 12)
    (lo := (71344269 / 500000000)) (hi := (142688539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9226964117229 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9226964117229 / 8000000000000) = 1/(500000000000 / 9226964117229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1457638629 / 500000000) (2915277263 / 1000000000) (Real.log (9226964117229 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9226964117229 / 500000000000) = -Real.log (500000000000 / 9226964117229) := by
    rw [show ((9226964117229 / 500000000000) : ℝ) = ((500000000000 / 9226964117229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (734328623 / 250000000) ≤ -Real.log (100000000000 / 1886511586329) ∧
    -Real.log (100000000000 / 1886511586329) ≤ (2937314497 / 1000000000) := by
  have h := checkLog_sound (w := (286511586329 / 3486511586329)) (n := 12)
    (lo := (41181443 / 250000000)) (hi := (164725773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1886511586329 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1886511586329 / 1600000000000) = 1/(100000000000 / 1886511586329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (734328623 / 250000000) (2937314497 / 1000000000) (Real.log (1886511586329 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1886511586329 / 100000000000) = -Real.log (100000000000 / 1886511586329) := by
    rw [show ((1886511586329 / 100000000000) : ℝ) = ((100000000000 / 1886511586329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0180

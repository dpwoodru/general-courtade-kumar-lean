import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3008_neg : (346835557 / 1000000000) ≤ -Real.log (250000000000 / 353646021973) ∧
    -Real.log (250000000000 / 353646021973) ≤ (173417779 / 500000000) := by
  have h := checkLog_sound (w := (103646021973 / 603646021973)) (n := 12)
    (lo := (346835557 / 1000000000)) (hi := (173417779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353646021973 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353646021973 / 250000000000) = 1/(250000000000 / 353646021973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3008 : Bounds (346835557 / 1000000000) (173417779 / 500000000) (Real.log (353646021973 / 250000000000)) := by
  have h := reflection_log_3008_neg
  have he : Real.log (353646021973 / 250000000000) = -Real.log (250000000000 / 353646021973) := by
    rw [show ((353646021973 / 250000000000) : ℝ) = ((250000000000 / 353646021973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3009_neg : (39635257 / 250000000) ≤ -Real.log (5000 / 5859) ∧
    -Real.log (5000 / 5859) ≤ (158541029 / 1000000000) := by
  have h := checkLog_sound (w := (859 / 10859)) (n := 12)
    (lo := (39635257 / 250000000)) (hi := (158541029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5859 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5859 / 5000) = 1/(5000 / 5859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3009 : Bounds (39635257 / 250000000) (158541029 / 1000000000) (Real.log (5859 / 5000)) := by
  have h := reflection_log_3009_neg
  have he : Real.log (5859 / 5000) = -Real.log (5000 / 5859) := by
    rw [show ((5859 / 5000) : ℝ) = ((5000 / 5859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3010_neg : (188500607 / 1000000000) ≤ -Real.log (4141 / 5000) ∧
    -Real.log (4141 / 5000) ≤ (1472661 / 7812500) := by
  have h := checkLog_sound (w := (859 / 9141)) (n := 12)
    (lo := (188500607 / 1000000000)) (hi := (1472661 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4141) = 1/(4141 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3010 : Bounds (-1472661 / 7812500) (-188500607 / 1000000000) (Real.log (4141 / 5000)) := by
  have h := reflection_log_3010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3011_neg : (34357 / 200000000) ≤ -Real.log (5000000 / 5000859) ∧
    -Real.log (5000000 / 5000859) ≤ (85893 / 500000000) := by
  have h := checkLog_sound (w := (859 / 10000859)) (n := 12)
    (lo := (34357 / 200000000)) (hi := (85893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000859 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000859 / 5000000) = 1/(5000000 / 5000859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3011 : Bounds (34357 / 200000000) (85893 / 500000000) (Real.log (5000859 / 5000000)) := by
  have h := reflection_log_3011_neg
  have he : Real.log (5000859 / 5000000) = -Real.log (5000000 / 5000859) := by
    rw [show ((5000859 / 5000000) : ℝ) = ((5000000 / 5000859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3012_neg : (85907 / 500000000) ≤ -Real.log (4999141 / 5000000) ∧
    -Real.log (4999141 / 5000000) ≤ (34363 / 200000000) := by
  have h := checkLog_sound (w := (859 / 9999141)) (n := 12)
    (lo := (85907 / 500000000)) (hi := (34363 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999141) = 1/(4999141 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3012 : Bounds (-34363 / 200000000) (-85907 / 500000000) (Real.log (4999141 / 5000000)) := by
  have h := reflection_log_3012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3013_neg : (41354191 / 500000000) ≤ -Real.log (40000 / 43449) ∧
    -Real.log (40000 / 43449) ≤ (82708383 / 1000000000) := by
  have h := checkLog_sound (w := (3449 / 83449)) (n := 12)
    (lo := (41354191 / 500000000)) (hi := (82708383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43449 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43449 / 40000) = 1/(40000 / 43449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3013 : Bounds (41354191 / 500000000) (82708383 / 1000000000) (Real.log (43449 / 40000)) := by
  have h := reflection_log_3013_neg
  have he : Real.log (43449 / 40000) = -Real.log (40000 / 43449) := by
    rw [show ((43449 / 40000) : ℝ) = ((40000 / 43449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3014_neg : (22542727 / 250000000) ≤ -Real.log (36551 / 40000) ∧
    -Real.log (36551 / 40000) ≤ (90170909 / 1000000000) := by
  have h := checkLog_sound (w := (3449 / 76551)) (n := 12)
    (lo := (22542727 / 250000000)) (hi := (90170909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36551) = 1/(36551 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3014 : Bounds (-90170909 / 1000000000) (-22542727 / 250000000) (Real.log (36551 / 40000)) := by
  have h := reflection_log_3014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3015_neg : (82912739 / 1000000000) ≤ -Real.log (1000000 / 1086447) ∧
    -Real.log (1000000 / 1086447) ≤ (4145637 / 50000000) := by
  have h := checkLog_sound (w := (86447 / 2086447)) (n := 12)
    (lo := (82912739 / 1000000000)) (hi := (4145637 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086447 / 1000000) = 1/(1000000 / 1086447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3015 : Bounds (82912739 / 1000000000) (4145637 / 50000000) (Real.log (1086447 / 1000000)) := by
  have h := reflection_log_3015_neg
  have he : Real.log (1086447 / 1000000) = -Real.log (1000000 / 1086447) := by
    rw [show ((1086447 / 1000000) : ℝ) = ((1000000 / 1086447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3016_neg : (45206943 / 500000000) ≤ -Real.log (913553 / 1000000) ∧
    -Real.log (913553 / 1000000) ≤ (90413887 / 1000000000) := by
  have h := checkLog_sound (w := (86447 / 1913553)) (n := 12)
    (lo := (45206943 / 500000000)) (hi := (90413887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913553) = 1/(913553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3016 : Bounds (-90413887 / 1000000000) (-45206943 / 500000000) (Real.log (913553 / 1000000)) := by
  have h := reflection_log_3016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3017_neg : (7501147 / 1000000000) ≤ -Real.log (992526916191 / 1000000000000) ∧
    -Real.log (992526916191 / 1000000000000) ≤ (1875287 / 250000000) := by
  have h := checkLog_sound (w := (7473083809 / 1992526916191)) (n := 12)
    (lo := (7501147 / 1000000000)) (hi := (1875287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992526916191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992526916191) = 1/(992526916191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3017 : Bounds (-1875287 / 250000000) (-7501147 / 1000000000) (Real.log (992526916191 / 1000000000000)) := by
  have h := reflection_log_3017_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3018_neg : (3731263 / 500000000) ≤ -Real.log (1588104399 / 1600000000) ∧
    -Real.log (1588104399 / 1600000000) ≤ (7462527 / 1000000000) := by
  have h := checkLog_sound (w := (11895601 / 3188104399)) (n := 12)
    (lo := (3731263 / 500000000)) (hi := (7462527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1588104399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1588104399) = 1/(1588104399 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3018 : Bounds (-7462527 / 1000000000) (-3731263 / 500000000) (Real.log (1588104399 / 1600000000)) := by
  have h := reflection_log_3018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3019_neg : (17287929 / 100000000) ≤ -Real.log (62500000000 / 74295162923) ∧
    -Real.log (62500000000 / 74295162923) ≤ (172879291 / 1000000000) := by
  have h := checkLog_sound (w := (11795162923 / 136795162923)) (n := 12)
    (lo := (17287929 / 100000000)) (hi := (172879291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74295162923 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74295162923 / 62500000000) = 1/(62500000000 / 74295162923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3019 : Bounds (17287929 / 100000000) (172879291 / 1000000000) (Real.log (74295162923 / 62500000000)) := by
  have h := reflection_log_3019_neg
  have he : Real.log (74295162923 / 62500000000) = -Real.log (62500000000 / 74295162923) := by
    rw [show ((74295162923 / 62500000000) : ℝ) = ((62500000000 / 74295162923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3020_neg : (1386613 / 8000000) ≤ -Real.log (500000000000 / 594627241113) ∧
    -Real.log (500000000000 / 594627241113) ≤ (86663313 / 500000000) := by
  have h := checkLog_sound (w := (94627241113 / 1094627241113)) (n := 12)
    (lo := (1386613 / 8000000)) (hi := (86663313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594627241113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594627241113 / 500000000000) = 1/(500000000000 / 594627241113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3020 : Bounds (1386613 / 8000000) (86663313 / 500000000) (Real.log (594627241113 / 500000000000)) := by
  have h := reflection_log_3020_neg
  have he : Real.log (594627241113 / 500000000000) = -Real.log (500000000000 / 594627241113) := by
    rw [show ((594627241113 / 500000000000) : ℝ) = ((500000000000 / 594627241113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3021_neg : (346835557 / 1000000000) ≤ -Real.log (100000000000 / 141458408789) ∧
    -Real.log (100000000000 / 141458408789) ≤ (173417779 / 500000000) := by
  have h := checkLog_sound (w := (41458408789 / 241458408789)) (n := 12)
    (lo := (346835557 / 1000000000)) (hi := (173417779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141458408789 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141458408789 / 100000000000) = 1/(100000000000 / 141458408789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3021 : Bounds (346835557 / 1000000000) (173417779 / 500000000) (Real.log (141458408789 / 100000000000)) := by
  have h := reflection_log_3021_neg
  have he : Real.log (141458408789 / 100000000000) = -Real.log (100000000000 / 141458408789) := by
    rw [show ((141458408789 / 100000000000) : ℝ) = ((100000000000 / 141458408789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3022_neg : (86760409 / 250000000) ≤ -Real.log (500000000000 / 707437816953) ∧
    -Real.log (500000000000 / 707437816953) ≤ (347041637 / 1000000000) := by
  have h := checkLog_sound (w := (207437816953 / 1207437816953)) (n := 12)
    (lo := (86760409 / 250000000)) (hi := (347041637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707437816953 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707437816953 / 500000000000) = 1/(500000000000 / 707437816953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3022 : Bounds (86760409 / 250000000) (347041637 / 1000000000) (Real.log (707437816953 / 500000000000)) := by
  have h := reflection_log_3022_neg
  have he : Real.log (707437816953 / 500000000000) = -Real.log (500000000000 / 707437816953) := by
    rw [show ((707437816953 / 500000000000) : ℝ) = ((500000000000 / 707437816953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3023_neg : (158626363 / 1000000000) ≤ -Real.log (10000 / 11719) ∧
    -Real.log (10000 / 11719) ≤ (39656591 / 250000000) := by
  have h := checkLog_sound (w := (1719 / 21719)) (n := 12)
    (lo := (158626363 / 1000000000)) (hi := (39656591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11719 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11719 / 10000) = 1/(10000 / 11719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3023 : Bounds (158626363 / 1000000000) (39656591 / 250000000) (Real.log (11719 / 10000)) := by
  have h := reflection_log_3023_neg
  have he : Real.log (11719 / 10000) = -Real.log (10000 / 11719) := by
    rw [show ((11719 / 10000) : ℝ) = ((10000 / 11719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3024_neg : (94310679 / 500000000) ≤ -Real.log (8281 / 10000) ∧
    -Real.log (8281 / 10000) ≤ (188621359 / 1000000000) := by
  have h := checkLog_sound (w := (1719 / 18281)) (n := 12)
    (lo := (94310679 / 500000000)) (hi := (188621359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8281) = 1/(8281 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3024 : Bounds (-188621359 / 1000000000) (-94310679 / 500000000) (Real.log (8281 / 10000)) := by
  have h := reflection_log_3024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3025_neg : (34377 / 200000000) ≤ -Real.log (10000000 / 10001719) ∧
    -Real.log (10000000 / 10001719) ≤ (85943 / 500000000) := by
  have h := checkLog_sound (w := (1719 / 20001719)) (n := 12)
    (lo := (34377 / 200000000)) (hi := (85943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001719 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001719 / 10000000) = 1/(10000000 / 10001719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3025 : Bounds (34377 / 200000000) (85943 / 500000000) (Real.log (10001719 / 10000000)) := by
  have h := reflection_log_3025_neg
  have he : Real.log (10001719 / 10000000) = -Real.log (10000000 / 10001719) := by
    rw [show ((10001719 / 10000000) : ℝ) = ((10000000 / 10001719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3026_neg : (85957 / 500000000) ≤ -Real.log (9998281 / 10000000) ∧
    -Real.log (9998281 / 10000000) ≤ (34383 / 200000000) := by
  have h := checkLog_sound (w := (1719 / 19998281)) (n := 12)
    (lo := (85957 / 500000000)) (hi := (34383 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998281) = 1/(9998281 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3026 : Bounds (-34383 / 200000000) (-85957 / 500000000) (Real.log (9998281 / 10000000)) := by
  have h := reflection_log_3026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3027_neg : (20688603 / 250000000) ≤ -Real.log (40000 / 43451) ∧
    -Real.log (40000 / 43451) ≤ (82754413 / 1000000000) := by
  have h := checkLog_sound (w := (3451 / 83451)) (n := 12)
    (lo := (20688603 / 250000000)) (hi := (82754413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43451 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43451 / 40000) = 1/(40000 / 43451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3027 : Bounds (20688603 / 250000000) (82754413 / 1000000000) (Real.log (43451 / 40000)) := by
  have h := reflection_log_3027_neg
  have he : Real.log (43451 / 40000) = -Real.log (40000 / 43451) := by
    rw [show ((43451 / 40000) : ℝ) = ((40000 / 43451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3028_neg : (22556407 / 250000000) ≤ -Real.log (36549 / 40000) ∧
    -Real.log (36549 / 40000) ≤ (90225629 / 1000000000) := by
  have h := checkLog_sound (w := (3451 / 76549)) (n := 12)
    (lo := (22556407 / 250000000)) (hi := (90225629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36549) = 1/(36549 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3028 : Bounds (-90225629 / 1000000000) (-22556407 / 250000000) (Real.log (36549 / 40000)) := by
  have h := reflection_log_3028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3029_neg : (82959679 / 1000000000) ≤ -Real.log (500000 / 543249) ∧
    -Real.log (500000 / 543249) ≤ (259249 / 3125000) := by
  have h := checkLog_sound (w := (43249 / 1043249)) (n := 12)
    (lo := (82959679 / 1000000000)) (hi := (259249 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543249 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543249 / 500000) = 1/(500000 / 543249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3029 : Bounds (82959679 / 1000000000) (259249 / 3125000) (Real.log (543249 / 500000)) := by
  have h := reflection_log_3029_neg
  have he : Real.log (543249 / 500000) = -Real.log (500000 / 543249) := by
    rw [show ((543249 / 500000) : ℝ) = ((500000 / 543249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3030_neg : (90469713 / 1000000000) ≤ -Real.log (456751 / 500000) ∧
    -Real.log (456751 / 500000) ≤ (45234857 / 500000000) := by
  have h := checkLog_sound (w := (43249 / 956751)) (n := 12)
    (lo := (90469713 / 1000000000)) (hi := (45234857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456751) = 1/(456751 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3030 : Bounds (-45234857 / 500000000) (-90469713 / 1000000000) (Real.log (456751 / 500000)) := by
  have h := reflection_log_3030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3031_neg : (7510033 / 1000000000) ≤ -Real.log (248129523999 / 250000000000) ∧
    -Real.log (248129523999 / 250000000000) ≤ (3755017 / 500000000) := by
  have h := checkLog_sound (w := (1870476001 / 498129523999)) (n := 12)
    (lo := (7510033 / 1000000000)) (hi := (3755017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248129523999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248129523999) = 1/(248129523999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3031 : Bounds (-3755017 / 500000000) (-7510033 / 1000000000) (Real.log (248129523999 / 250000000000)) := by
  have h := reflection_log_3031_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3032_neg : (1494243 / 200000000) ≤ -Real.log (1588090599 / 1600000000) ∧
    -Real.log (1588090599 / 1600000000) ≤ (466951 / 62500000) := by
  have h := checkLog_sound (w := (11909401 / 3188090599)) (n := 12)
    (lo := (1494243 / 200000000)) (hi := (466951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1588090599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1588090599) = 1/(1588090599 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3032 : Bounds (-466951 / 62500000) (-1494243 / 200000000) (Real.log (1588090599 / 1600000000)) := by
  have h := reflection_log_3032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3033_neg : (4324501 / 25000000) ≤ -Real.log (250000000000 / 297210593997) ∧
    -Real.log (250000000000 / 297210593997) ≤ (172980041 / 1000000000) := by
  have h := checkLog_sound (w := (47210593997 / 547210593997)) (n := 12)
    (lo := (4324501 / 25000000)) (hi := (172980041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297210593997 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297210593997 / 250000000000) = 1/(250000000000 / 297210593997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3033 : Bounds (4324501 / 25000000) (172980041 / 1000000000) (Real.log (297210593997 / 250000000000)) := by
  have h := reflection_log_3033_neg
  have he : Real.log (297210593997 / 250000000000) = -Real.log (250000000000 / 297210593997) := by
    rw [show ((297210593997 / 250000000000) : ℝ) = ((250000000000 / 297210593997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3034_neg : (173429393 / 1000000000) ≤ -Real.log (500000000000 / 594688353173) ∧
    -Real.log (500000000000 / 594688353173) ≤ (86714697 / 500000000) := by
  have h := checkLog_sound (w := (94688353173 / 1094688353173)) (n := 12)
    (lo := (173429393 / 1000000000)) (hi := (86714697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594688353173 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594688353173 / 500000000000) = 1/(500000000000 / 594688353173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3034 : Bounds (173429393 / 1000000000) (86714697 / 500000000) (Real.log (594688353173 / 500000000000)) := by
  have h := reflection_log_3034_neg
  have he : Real.log (594688353173 / 500000000000) = -Real.log (500000000000 / 594688353173) := by
    rw [show ((594688353173 / 500000000000) : ℝ) = ((500000000000 / 594688353173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3035_neg : (69408327 / 200000000) ≤ -Real.log (62500000000 / 88429727119) ∧
    -Real.log (62500000000 / 88429727119) ≤ (86760409 / 250000000) := by
  have h := checkLog_sound (w := (25929727119 / 150929727119)) (n := 12)
    (lo := (69408327 / 200000000)) (hi := (86760409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88429727119 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88429727119 / 62500000000) = 1/(62500000000 / 88429727119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3035 : Bounds (69408327 / 200000000) (86760409 / 250000000) (Real.log (88429727119 / 62500000000)) := by
  have h := reflection_log_3035_neg
  have he : Real.log (88429727119 / 62500000000) = -Real.log (62500000000 / 88429727119) := by
    rw [show ((88429727119 / 62500000000) : ℝ) = ((62500000000 / 88429727119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3036_neg : (173623861 / 500000000) ≤ -Real.log (500000000000 / 707583625167) ∧
    -Real.log (500000000000 / 707583625167) ≤ (347247723 / 1000000000) := by
  have h := checkLog_sound (w := (207583625167 / 1207583625167)) (n := 12)
    (lo := (173623861 / 500000000)) (hi := (347247723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707583625167 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707583625167 / 500000000000) = 1/(500000000000 / 707583625167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3036 : Bounds (173623861 / 500000000) (347247723 / 1000000000) (Real.log (707583625167 / 500000000000)) := by
  have h := reflection_log_3036_neg
  have he : Real.log (707583625167 / 500000000000) = -Real.log (500000000000 / 707583625167) := by
    rw [show ((707583625167 / 500000000000) : ℝ) = ((500000000000 / 707583625167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3037_neg : (158711691 / 1000000000) ≤ -Real.log (250 / 293) ∧
    -Real.log (250 / 293) ≤ (39677923 / 250000000) := by
  have h := checkLog_sound (w := (43 / 543)) (n := 12)
    (lo := (158711691 / 1000000000)) (hi := (39677923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293 / 250) = 1/(250 / 293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3037 : Bounds (158711691 / 1000000000) (39677923 / 250000000) (Real.log (293 / 250)) := by
  have h := reflection_log_3037_neg
  have he : Real.log (293 / 250) = -Real.log (250 / 293) := by
    rw [show ((293 / 250) : ℝ) = ((250 / 293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3038_neg : (47185531 / 250000000) ≤ -Real.log (207 / 250) ∧
    -Real.log (207 / 250) ≤ (1509937 / 8000000) := by
  have h := checkLog_sound (w := (43 / 457)) (n := 12)
    (lo := (47185531 / 250000000)) (hi := (1509937 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 207) = 1/(207 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3038 : Bounds (-1509937 / 8000000) (-47185531 / 250000000) (Real.log (207 / 250)) := by
  have h := reflection_log_3038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3039_neg : (34397 / 200000000) ≤ -Real.log (250000 / 250043) ∧
    -Real.log (250000 / 250043) ≤ (85993 / 500000000) := by
  have h := checkLog_sound (w := (43 / 500043)) (n := 12)
    (lo := (34397 / 200000000)) (hi := (85993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250043 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250043 / 250000) = 1/(250000 / 250043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3039 : Bounds (34397 / 200000000) (85993 / 500000000) (Real.log (250043 / 250000)) := by
  have h := reflection_log_3039_neg
  have he : Real.log (250043 / 250000) = -Real.log (250000 / 250043) := by
    rw [show ((250043 / 250000) : ℝ) = ((250000 / 250043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3040_neg : (86007 / 500000000) ≤ -Real.log (249957 / 250000) ∧
    -Real.log (249957 / 250000) ≤ (34403 / 200000000) := by
  have h := checkLog_sound (w := (43 / 499957)) (n := 12)
    (lo := (86007 / 500000000)) (hi := (34403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249957) = 1/(249957 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3040 : Bounds (-34403 / 200000000) (-86007 / 500000000) (Real.log (249957 / 250000)) := by
  have h := reflection_log_3040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3041_neg : (1035017 / 12500000) ≤ -Real.log (500000 / 543163) ∧
    -Real.log (500000 / 543163) ≤ (82801361 / 1000000000) := by
  have h := checkLog_sound (w := (43163 / 1043163)) (n := 12)
    (lo := (1035017 / 12500000)) (hi := (82801361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543163 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543163 / 500000) = 1/(500000 / 543163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3041 : Bounds (1035017 / 12500000) (82801361 / 1000000000) (Real.log (543163 / 500000)) := by
  have h := reflection_log_3041_neg
  have he : Real.log (543163 / 500000) = -Real.log (500000 / 543163) := by
    rw [show ((543163 / 500000) : ℝ) = ((500000 / 543163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3042_neg : (18056289 / 200000000) ≤ -Real.log (456837 / 500000) ∧
    -Real.log (456837 / 500000) ≤ (45140723 / 500000000) := by
  have h := checkLog_sound (w := (43163 / 956837)) (n := 12)
    (lo := (18056289 / 200000000)) (hi := (45140723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456837) = 1/(456837 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3042 : Bounds (-45140723 / 500000000) (-18056289 / 200000000) (Real.log (456837 / 500000)) := by
  have h := reflection_log_3042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3043_neg : (41503309 / 500000000) ≤ -Real.log (1000000 / 1086549) ∧
    -Real.log (1000000 / 1086549) ≤ (83006619 / 1000000000) := by
  have h := checkLog_sound (w := (86549 / 2086549)) (n := 12)
    (lo := (41503309 / 500000000)) (hi := (83006619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086549 / 1000000) = 1/(1000000 / 1086549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3043 : Bounds (41503309 / 500000000) (83006619 / 1000000000) (Real.log (1086549 / 1000000)) := by
  have h := reflection_log_3043_neg
  have he : Real.log (1086549 / 1000000) = -Real.log (1000000 / 1086549) := by
    rw [show ((1086549 / 1000000) : ℝ) = ((1000000 / 1086549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3044_neg : (11315693 / 125000000) ≤ -Real.log (913451 / 1000000) ∧
    -Real.log (913451 / 1000000) ≤ (18105109 / 200000000) := by
  have h := checkLog_sound (w := (86549 / 1913451)) (n := 12)
    (lo := (11315693 / 125000000)) (hi := (18105109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913451) = 1/(913451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3044 : Bounds (-18105109 / 200000000) (-11315693 / 125000000) (Real.log (913451 / 1000000)) := by
  have h := reflection_log_3044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3045_neg : (300757 / 40000000) ≤ -Real.log (992509270599 / 1000000000000) ∧
    -Real.log (992509270599 / 1000000000000) ≤ (3759463 / 500000000) := by
  have h := checkLog_sound (w := (7490729401 / 1992509270599)) (n := 12)
    (lo := (300757 / 40000000)) (hi := (3759463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992509270599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992509270599) = 1/(992509270599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3045 : Bounds (-3759463 / 500000000) (-300757 / 40000000) (Real.log (992509270599 / 1000000000000)) := by
  have h := reflection_log_3045_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3046_neg : (1870021 / 250000000) ≤ -Real.log (248136955431 / 250000000000) ∧
    -Real.log (248136955431 / 250000000000) ≤ (1496017 / 200000000) := by
  have h := checkLog_sound (w := (1863044569 / 498136955431)) (n := 12)
    (lo := (1870021 / 250000000)) (hi := (1496017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248136955431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248136955431) = 1/(248136955431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3046 : Bounds (-1496017 / 200000000) (-1870021 / 250000000) (Real.log (248136955431 / 250000000000)) := by
  have h := reflection_log_3046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3047_neg : (34616561 / 200000000) ≤ -Real.log (62500000000 / 74310284631) ∧
    -Real.log (62500000000 / 74310284631) ≤ (86541403 / 500000000) := by
  have h := checkLog_sound (w := (11810284631 / 136810284631)) (n := 12)
    (lo := (34616561 / 200000000)) (hi := (86541403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74310284631 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74310284631 / 62500000000) = 1/(62500000000 / 74310284631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3047 : Bounds (34616561 / 200000000) (86541403 / 500000000) (Real.log (74310284631 / 62500000000)) := by
  have h := reflection_log_3047_neg
  have he : Real.log (74310284631 / 62500000000) = -Real.log (62500000000 / 74310284631) := by
    rw [show ((74310284631 / 62500000000) : ℝ) = ((62500000000 / 74310284631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3048_neg : (173532163 / 1000000000) ≤ -Real.log (250000000000 / 297374736029) ∧
    -Real.log (250000000000 / 297374736029) ≤ (43383041 / 250000000) := by
  have h := checkLog_sound (w := (47374736029 / 547374736029)) (n := 12)
    (lo := (173532163 / 1000000000)) (hi := (43383041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297374736029 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297374736029 / 250000000000) = 1/(250000000000 / 297374736029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3048 : Bounds (173532163 / 1000000000) (43383041 / 250000000) (Real.log (297374736029 / 250000000000)) := by
  have h := reflection_log_3048_neg
  have he : Real.log (297374736029 / 250000000000) = -Real.log (250000000000 / 297374736029) := by
    rw [show ((297374736029 / 250000000000) : ℝ) = ((250000000000 / 297374736029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3049_neg : (173623861 / 500000000) ≤ -Real.log (250000000000 / 353791812583) ∧
    -Real.log (250000000000 / 353791812583) ≤ (347247723 / 1000000000) := by
  have h := checkLog_sound (w := (103791812583 / 603791812583)) (n := 12)
    (lo := (173623861 / 500000000)) (hi := (347247723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353791812583 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353791812583 / 250000000000) = 1/(250000000000 / 353791812583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3049 : Bounds (173623861 / 500000000) (347247723 / 1000000000) (Real.log (353791812583 / 250000000000)) := by
  have h := reflection_log_3049_neg
  have he : Real.log (353791812583 / 250000000000) = -Real.log (250000000000 / 353791812583) := by
    rw [show ((353791812583 / 250000000000) : ℝ) = ((250000000000 / 353791812583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3050_neg : (69490763 / 200000000) ≤ -Real.log (2500000000 / 3538647343) ∧
    -Real.log (2500000000 / 3538647343) ≤ (43431727 / 125000000) := by
  have h := checkLog_sound (w := (1038647343 / 6038647343)) (n := 12)
    (lo := (69490763 / 200000000)) (hi := (43431727 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3538647343 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3538647343 / 2500000000) = 1/(2500000000 / 3538647343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3050 : Bounds (69490763 / 200000000) (43431727 / 125000000) (Real.log (3538647343 / 2500000000)) := by
  have h := reflection_log_3050_neg
  have he : Real.log (3538647343 / 2500000000) = -Real.log (2500000000 / 3538647343) := by
    rw [show ((3538647343 / 2500000000) : ℝ) = ((2500000000 / 3538647343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3051_neg : (158797011 / 1000000000) ≤ -Real.log (10000 / 11721) ∧
    -Real.log (10000 / 11721) ≤ (39699253 / 250000000) := by
  have h := checkLog_sound (w := (1721 / 21721)) (n := 12)
    (lo := (158797011 / 1000000000)) (hi := (39699253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11721 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11721 / 10000) = 1/(10000 / 11721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3051 : Bounds (158797011 / 1000000000) (39699253 / 250000000) (Real.log (11721 / 10000)) := by
  have h := reflection_log_3051_neg
  have he : Real.log (11721 / 10000) = -Real.log (10000 / 11721) := by
    rw [show ((11721 / 10000) : ℝ) = ((10000 / 11721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3052_neg : (23607863 / 125000000) ≤ -Real.log (8279 / 10000) ∧
    -Real.log (8279 / 10000) ≤ (37772581 / 200000000) := by
  have h := checkLog_sound (w := (1721 / 18279)) (n := 12)
    (lo := (23607863 / 125000000)) (hi := (37772581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8279) = 1/(8279 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3052 : Bounds (-37772581 / 200000000) (-23607863 / 125000000) (Real.log (8279 / 10000)) := by
  have h := reflection_log_3052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3053_neg : (34417 / 200000000) ≤ -Real.log (10000000 / 10001721) ∧
    -Real.log (10000000 / 10001721) ≤ (86043 / 500000000) := by
  have h := checkLog_sound (w := (1721 / 20001721)) (n := 12)
    (lo := (34417 / 200000000)) (hi := (86043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001721 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001721 / 10000000) = 1/(10000000 / 10001721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3053 : Bounds (34417 / 200000000) (86043 / 500000000) (Real.log (10001721 / 10000000)) := by
  have h := reflection_log_3053_neg
  have he : Real.log (10001721 / 10000000) = -Real.log (10000000 / 10001721) := by
    rw [show ((10001721 / 10000000) : ℝ) = ((10000000 / 10001721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3054_neg : (86057 / 500000000) ≤ -Real.log (9998279 / 10000000) ∧
    -Real.log (9998279 / 10000000) ≤ (34423 / 200000000) := by
  have h := checkLog_sound (w := (1721 / 19998279)) (n := 12)
    (lo := (86057 / 500000000)) (hi := (34423 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998279) = 1/(9998279 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3054 : Bounds (-34423 / 200000000) (-86057 / 500000000) (Real.log (9998279 / 10000000)) := by
  have h := reflection_log_3054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3055_neg : (41424153 / 500000000) ≤ -Real.log (1000000 / 1086377) ∧
    -Real.log (1000000 / 1086377) ≤ (82848307 / 1000000000) := by
  have h := checkLog_sound (w := (86377 / 2086377)) (n := 12)
    (lo := (41424153 / 500000000)) (hi := (82848307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086377 / 1000000) = 1/(1000000 / 1086377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3055 : Bounds (41424153 / 500000000) (82848307 / 1000000000) (Real.log (1086377 / 1000000)) := by
  have h := reflection_log_3055_neg
  have he : Real.log (1086377 / 1000000) = -Real.log (1000000 / 1086377) := by
    rw [show ((1086377 / 1000000) : ℝ) = ((1000000 / 1086377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3056_neg : (18067453 / 200000000) ≤ -Real.log (913623 / 1000000) ∧
    -Real.log (913623 / 1000000) ≤ (45168633 / 500000000) := by
  have h := checkLog_sound (w := (86377 / 1913623)) (n := 12)
    (lo := (18067453 / 200000000)) (hi := (45168633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913623) = 1/(913623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3056 : Bounds (-45168633 / 500000000) (-18067453 / 200000000) (Real.log (913623 / 1000000)) := by
  have h := reflection_log_3056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3057_neg : (16610711 / 200000000) ≤ -Real.log (5000 / 5433) ∧
    -Real.log (5000 / 5433) ≤ (20763389 / 250000000) := by
  have h := checkLog_sound (w := (433 / 10433)) (n := 12)
    (lo := (16610711 / 200000000)) (hi := (20763389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5433 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5433 / 5000) = 1/(5000 / 5433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3057 : Bounds (16610711 / 200000000) (20763389 / 250000000) (Real.log (5433 / 5000)) := by
  have h := reflection_log_3057_neg
  have he : Real.log (5433 / 5000) = -Real.log (5000 / 5433) := by
    rw [show ((5433 / 5000) : ℝ) = ((5000 / 5433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3058_neg : (45290689 / 500000000) ≤ -Real.log (4567 / 5000) ∧
    -Real.log (4567 / 5000) ≤ (90581379 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 9567)) (n := 12)
    (lo := (45290689 / 500000000)) (hi := (90581379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4567) = 1/(4567 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3058 : Bounds (-90581379 / 1000000000) (-45290689 / 500000000) (Real.log (4567 / 5000)) := by
  have h := reflection_log_3058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3059_neg : (7527823 / 1000000000) ≤ -Real.log (24812511 / 25000000) ∧
    -Real.log (24812511 / 25000000) ≤ (470489 / 62500000) := by
  have h := checkLog_sound (w := (187489 / 49812511)) (n := 12)
    (lo := (7527823 / 1000000000)) (hi := (470489 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000000 / 24812511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000000 / 24812511) = 1/(24812511 / 25000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3059 : Bounds (-470489 / 62500000) (-7527823 / 1000000000) (Real.log (24812511 / 25000000)) := by
  have h := reflection_log_3059_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3060_neg : (3744479 / 500000000) ≤ -Real.log (992539013871 / 1000000000000) ∧
    -Real.log (992539013871 / 1000000000000) ≤ (7488959 / 1000000000) := by
  have h := checkLog_sound (w := (7460986129 / 1992539013871)) (n := 12)
    (lo := (3744479 / 500000000)) (hi := (7488959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992539013871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992539013871) = 1/(992539013871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3060 : Bounds (-7488959 / 1000000000) (-3744479 / 500000000) (Real.log (992539013871 / 1000000000000)) := by
  have h := reflection_log_3060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3061_neg : (43296393 / 250000000) ≤ -Real.log (250000000000 / 297271686461) ∧
    -Real.log (250000000000 / 297271686461) ≤ (173185573 / 1000000000) := by
  have h := checkLog_sound (w := (47271686461 / 547271686461)) (n := 12)
    (lo := (43296393 / 250000000)) (hi := (173185573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297271686461 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297271686461 / 250000000000) = 1/(250000000000 / 297271686461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3061 : Bounds (43296393 / 250000000) (173185573 / 1000000000) (Real.log (297271686461 / 250000000000)) := by
  have h := reflection_log_3061_neg
  have he : Real.log (297271686461 / 250000000000) = -Real.log (250000000000 / 297271686461) := by
    rw [show ((297271686461 / 250000000000) : ℝ) = ((250000000000 / 297271686461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3062_neg : (173634933 / 1000000000) ≤ -Real.log (500000000000 / 594810597767) ∧
    -Real.log (500000000000 / 594810597767) ≤ (86817467 / 500000000) := by
  have h := checkLog_sound (w := (94810597767 / 1094810597767)) (n := 12)
    (lo := (173634933 / 1000000000)) (hi := (86817467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594810597767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594810597767 / 500000000000) = 1/(500000000000 / 594810597767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3062 : Bounds (173634933 / 1000000000) (86817467 / 500000000) (Real.log (594810597767 / 500000000000)) := by
  have h := reflection_log_3062_neg
  have he : Real.log (594810597767 / 500000000000) = -Real.log (500000000000 / 594810597767) := by
    rw [show ((594810597767 / 500000000000) : ℝ) = ((500000000000 / 594810597767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3063_neg : (69490763 / 200000000) ≤ -Real.log (500000000000 / 707729468599) ∧
    -Real.log (500000000000 / 707729468599) ≤ (43431727 / 125000000) := by
  have h := checkLog_sound (w := (207729468599 / 1207729468599)) (n := 12)
    (lo := (69490763 / 200000000)) (hi := (43431727 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707729468599 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707729468599 / 500000000000) = 1/(500000000000 / 707729468599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3063 : Bounds (69490763 / 200000000) (43431727 / 125000000) (Real.log (707729468599 / 500000000000)) := by
  have h := reflection_log_3063_neg
  have he : Real.log (707729468599 / 500000000000) = -Real.log (500000000000 / 707729468599) := by
    rw [show ((707729468599 / 500000000000) : ℝ) = ((500000000000 / 707729468599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3064_neg : (86914979 / 250000000) ≤ -Real.log (100000000000 / 141575069453) ∧
    -Real.log (100000000000 / 141575069453) ≤ (347659917 / 1000000000) := by
  have h := checkLog_sound (w := (41575069453 / 241575069453)) (n := 12)
    (lo := (86914979 / 250000000)) (hi := (347659917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141575069453 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141575069453 / 100000000000) = 1/(100000000000 / 141575069453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3064 : Bounds (86914979 / 250000000) (347659917 / 1000000000) (Real.log (141575069453 / 100000000000)) := by
  have h := reflection_log_3064_neg
  have he : Real.log (141575069453 / 100000000000) = -Real.log (100000000000 / 141575069453) := by
    rw [show ((141575069453 / 100000000000) : ℝ) = ((100000000000 / 141575069453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3065_neg : (6355293 / 40000000) ≤ -Real.log (5000 / 5861) ∧
    -Real.log (5000 / 5861) ≤ (79441163 / 500000000) := by
  have h := checkLog_sound (w := (861 / 10861)) (n := 12)
    (lo := (6355293 / 40000000)) (hi := (79441163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5861 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5861 / 5000) = 1/(5000 / 5861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3065 : Bounds (6355293 / 40000000) (79441163 / 500000000) (Real.log (5861 / 5000)) := by
  have h := reflection_log_3065_neg
  have he : Real.log (5861 / 5000) = -Real.log (5000 / 5861) := by
    rw [show ((5861 / 5000) : ℝ) = ((5000 / 5861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3066_neg : (188983699 / 1000000000) ≤ -Real.log (4139 / 5000) ∧
    -Real.log (4139 / 5000) ≤ (1889837 / 10000000) := by
  have h := checkLog_sound (w := (861 / 9139)) (n := 12)
    (lo := (188983699 / 1000000000)) (hi := (1889837 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4139) = 1/(4139 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3066 : Bounds (-1889837 / 10000000) (-188983699 / 1000000000) (Real.log (4139 / 5000)) := by
  have h := reflection_log_3066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3067_neg : (34437 / 200000000) ≤ -Real.log (5000000 / 5000861) ∧
    -Real.log (5000000 / 5000861) ≤ (86093 / 500000000) := by
  have h := checkLog_sound (w := (861 / 10000861)) (n := 12)
    (lo := (34437 / 200000000)) (hi := (86093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000861 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000861 / 5000000) = 1/(5000000 / 5000861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3067 : Bounds (34437 / 200000000) (86093 / 500000000) (Real.log (5000861 / 5000000)) := by
  have h := reflection_log_3067_neg
  have he : Real.log (5000861 / 5000000) = -Real.log (5000000 / 5000861) := by
    rw [show ((5000861 / 5000000) : ℝ) = ((5000000 / 5000861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3068_neg : (86107 / 500000000) ≤ -Real.log (4999139 / 5000000) ∧
    -Real.log (4999139 / 5000000) ≤ (34443 / 200000000) := by
  have h := checkLog_sound (w := (861 / 9999139)) (n := 12)
    (lo := (86107 / 500000000)) (hi := (34443 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999139) = 1/(4999139 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3068 : Bounds (-34443 / 200000000) (-86107 / 500000000) (Real.log (4999139 / 5000000)) := by
  have h := reflection_log_3068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3069_neg : (331581 / 4000000) ≤ -Real.log (250000 / 271607) ∧
    -Real.log (250000 / 271607) ≤ (82895251 / 1000000000) := by
  have h := checkLog_sound (w := (21607 / 521607)) (n := 12)
    (lo := (331581 / 4000000)) (hi := (82895251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271607 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271607 / 250000) = 1/(250000 / 271607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3069 : Bounds (331581 / 4000000) (82895251 / 1000000000) (Real.log (271607 / 250000)) := by
  have h := reflection_log_3069_neg
  have he : Real.log (271607 / 250000) = -Real.log (250000 / 271607) := by
    rw [show ((271607 / 250000) : ℝ) = ((250000 / 271607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3070_neg : (176549 / 1953125) ≤ -Real.log (228393 / 250000) ∧
    -Real.log (228393 / 250000) ≤ (90393089 / 1000000000) := by
  have h := checkLog_sound (w := (21607 / 478393)) (n := 12)
    (lo := (176549 / 1953125)) (hi := (90393089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228393) = 1/(228393 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3070 : Bounds (-90393089 / 1000000000) (-176549 / 1953125) (Real.log (228393 / 250000)) := by
  have h := reflection_log_3070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3071_neg : (83100489 / 1000000000) ≤ -Real.log (1000000 / 1086651) ∧
    -Real.log (1000000 / 1086651) ≤ (8310049 / 100000000) := by
  have h := checkLog_sound (w := (86651 / 2086651)) (n := 12)
    (lo := (83100489 / 1000000000)) (hi := (8310049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086651 / 1000000) = 1/(1000000 / 1086651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3071 : Bounds (83100489 / 1000000000) (8310049 / 100000000) (Real.log (1086651 / 1000000)) := by
  have h := reflection_log_3071_neg
  have he : Real.log (1086651 / 1000000) = -Real.log (1000000 / 1086651) := by
    rw [show ((1086651 / 1000000) : ℝ) = ((1000000 / 1086651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13760_neg : (278483649 / 500000000) ≤ -Real.log (35809 / 62500) ∧
    -Real.log (35809 / 62500) ≤ (556967299 / 1000000000) := by
  have h := checkLog_sound (w := (26691 / 98309)) (n := 12)
    (lo := (278483649 / 500000000)) (hi := (556967299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 35809) = 1/(35809 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13760 : Bounds (-556967299 / 1000000000) (-278483649 / 500000000) (Real.log (35809 / 62500)) := by
  have h := reflection_log_13760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13761_neg : (357594021 / 1000000000) ≤ -Real.log (200000 / 285977) ∧
    -Real.log (200000 / 285977) ≤ (178797011 / 500000000) := by
  have h := checkLog_sound (w := (85977 / 485977)) (n := 12)
    (lo := (357594021 / 1000000000)) (hi := (178797011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((285977 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(285977 / 200000) = 1/(200000 / 285977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13761 : Bounds (357594021 / 1000000000) (178797011 / 500000000) (Real.log (285977 / 200000)) := by
  have h := reflection_log_13761_neg
  have he : Real.log (285977 / 200000) = -Real.log (200000 / 285977) := by
    rw [show ((285977 / 200000) : ℝ) = ((200000 / 285977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13762_neg : (2194989 / 3906250) ≤ -Real.log (114023 / 200000) ∧
    -Real.log (114023 / 200000) ≤ (112383437 / 200000000) := by
  have h := checkLog_sound (w := (85977 / 314023)) (n := 12)
    (lo := (2194989 / 3906250)) (hi := (112383437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 114023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 114023) = 1/(114023 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13762 : Bounds (-112383437 / 200000000) (-2194989 / 3906250) (Real.log (114023 / 200000)) := by
  have h := reflection_log_13762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13763_neg : (102161581 / 500000000) ≤ -Real.log (32607955471 / 40000000000) ∧
    -Real.log (32607955471 / 40000000000) ≤ (204323163 / 1000000000) := by
  have h := checkLog_sound (w := (7392044529 / 72607955471)) (n := 12)
    (lo := (102161581 / 500000000)) (hi := (204323163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 32607955471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 32607955471) = 1/(32607955471 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13763 : Bounds (-204323163 / 1000000000) (-102161581 / 500000000) (Real.log (32607955471 / 40000000000)) := by
  have h := reflection_log_13763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13764_neg : (201353717 / 1000000000) ≤ -Real.log (3193840519 / 3906250000) ∧
    -Real.log (3193840519 / 3906250000) ≤ (100676859 / 500000000) := by
  have h := checkLog_sound (w := (712409481 / 7100090519)) (n := 12)
    (lo := (201353717 / 1000000000)) (hi := (100676859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3193840519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3193840519) = 1/(3193840519 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13764 : Bounds (-100676859 / 500000000) (-201353717 / 1000000000) (Real.log (3193840519 / 3906250000)) := by
  have h := reflection_log_13764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13765_neg : (456290439 / 500000000) ≤ -Real.log (500000000000 / 1245371275377) ∧
    -Real.log (500000000000 / 1245371275377) ≤ (11407261 / 12500000) := by
  have h := checkLog_sound (w := (245371275377 / 2245371275377)) (n := 12)
    (lo := (109716849 / 500000000)) (hi := (219433699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245371275377 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1245371275377 / 1000000000000) = 1/(500000000000 / 1245371275377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13765 : Bounds (456290439 / 500000000) (11407261 / 12500000) (Real.log (1245371275377 / 500000000000)) := by
  have h := reflection_log_13765_neg
  have he : Real.log (1245371275377 / 500000000000) = -Real.log (500000000000 / 1245371275377) := by
    rw [show ((1245371275377 / 500000000000) : ℝ) = ((500000000000 / 1245371275377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13766_neg : (183902241 / 200000000) ≤ -Real.log (500000000000 / 1254032081247) ∧
    -Real.log (500000000000 / 1254032081247) ≤ (919511207 / 1000000000) := by
  have h := checkLog_sound (w := (254032081247 / 2254032081247)) (n := 12)
    (lo := (9054561 / 40000000)) (hi := (113182013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254032081247 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1254032081247 / 1000000000000) = 1/(500000000000 / 1254032081247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13766 : Bounds (183902241 / 200000000) (919511207 / 1000000000) (Real.log (1254032081247 / 500000000000)) := by
  have h := reflection_log_13766_neg
  have he : Real.log (1254032081247 / 500000000000) = -Real.log (500000000000 / 1254032081247) := by
    rw [show ((1254032081247 / 500000000000) : ℝ) = ((500000000000 / 1254032081247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13767_neg : (39659887 / 20000000) ≤ -Real.log (250000000000 / 1816115702479) ∧
    -Real.log (250000000000 / 1816115702479) ≤ (1982994353 / 1000000000) := by
  have h := checkLog_sound (w := (816115702479 / 2816115702479)) (n := 12)
    (lo := (59669999 / 100000000)) (hi := (596699991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1816115702479 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1816115702479 / 1000000000000) = 1/(250000000000 / 1816115702479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13767 : Bounds (39659887 / 20000000) (1982994353 / 1000000000) (Real.log (1816115702479 / 250000000000)) := by
  have h := reflection_log_13767_neg
  have he : Real.log (1816115702479 / 250000000000) = -Real.log (250000000000 / 1816115702479) := by
    rw [show ((1816115702479 / 250000000000) : ℝ) = ((250000000000 / 1816115702479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13768_neg : (399434711 / 200000000) ≤ -Real.log (500000000000 / 3684100418411) ∧
    -Real.log (500000000000 / 3684100418411) ≤ (998586779 / 500000000) := by
  have h := checkLog_sound (w := (1684100418411 / 5684100418411)) (n := 12)
    (lo := (122175839 / 200000000)) (hi := (152719799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3684100418411 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3684100418411 / 2000000000000) = 1/(500000000000 / 3684100418411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13768 : Bounds (399434711 / 200000000) (998586779 / 500000000) (Real.log (3684100418411 / 500000000000)) := by
  have h := reflection_log_13768_neg
  have he : Real.log (3684100418411 / 500000000000) = -Real.log (500000000000 / 3684100418411) := by
    rw [show ((3684100418411 / 500000000000) : ℝ) = ((500000000000 / 3684100418411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13769_neg : (567583957 / 1000000000) ≤ -Real.log (250 / 441) ∧
    -Real.log (250 / 441) ≤ (283791979 / 500000000) := by
  have h := checkLog_sound (w := (191 / 691)) (n := 12)
    (lo := (567583957 / 1000000000)) (hi := (283791979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441 / 250) = 1/(250 / 441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13769 : Bounds (567583957 / 1000000000) (283791979 / 500000000) (Real.log (441 / 250)) := by
  have h := reflection_log_13769_neg
  have he : Real.log (441 / 250) = -Real.log (250 / 441) := by
    rw [show ((441 / 250) : ℝ) = ((250 / 441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13770_neg : (90245217 / 62500000) ≤ -Real.log (59 / 250) ∧
    -Real.log (59 / 250) ≤ (57756939 / 40000000) := by
  have h := checkLog_sound (w := (7 / 243)) (n := 12)
    (lo := (7203639 / 125000000)) (hi := (57629113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 118) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 118) = 1/(59 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13770 : Bounds (-57756939 / 40000000) (-90245217 / 62500000) (Real.log (59 / 250)) := by
  have h := reflection_log_13770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13771_neg : (190927 / 250000000) ≤ -Real.log (250000 / 250191) ∧
    -Real.log (250000 / 250191) ≤ (763709 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 500191)) (n := 12)
    (lo := (190927 / 250000000)) (hi := (763709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250191 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250191 / 250000) = 1/(250000 / 250191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13771 : Bounds (190927 / 250000000) (763709 / 1000000000) (Real.log (250191 / 250000)) := by
  have h := reflection_log_13771_neg
  have he : Real.log (250191 / 250000) = -Real.log (250000 / 250191) := by
    rw [show ((250191 / 250000) : ℝ) = ((250000 / 250191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13772_neg : (764291 / 1000000000) ≤ -Real.log (249809 / 250000) ∧
    -Real.log (249809 / 250000) ≤ (191073 / 250000000) := by
  have h := checkLog_sound (w := (191 / 499809)) (n := 12)
    (lo := (764291 / 1000000000)) (hi := (191073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249809) = 1/(249809 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13772 : Bounds (-191073 / 250000000) (-764291 / 1000000000) (Real.log (249809 / 250000)) := by
  have h := reflection_log_13772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13773_neg : (71428287 / 200000000) ≤ -Real.log (500000 / 714619) ∧
    -Real.log (500000 / 714619) ≤ (89285359 / 250000000) := by
  have h := checkLog_sound (w := (214619 / 1214619)) (n := 12)
    (lo := (71428287 / 200000000)) (hi := (89285359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714619 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714619 / 500000) = 1/(500000 / 714619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13773 : Bounds (71428287 / 200000000) (89285359 / 250000000) (Real.log (714619 / 500000)) := by
  have h := reflection_log_13773_neg
  have he : Real.log (714619 / 500000) = -Real.log (500000 / 714619) := by
    rw [show ((714619 / 500000) : ℝ) = ((500000 / 714619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13774_neg : (70097871 / 125000000) ≤ -Real.log (285381 / 500000) ∧
    -Real.log (285381 / 500000) ≤ (560782969 / 1000000000) := by
  have h := checkLog_sound (w := (214619 / 785381)) (n := 12)
    (lo := (70097871 / 125000000)) (hi := (560782969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 285381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 285381) = 1/(285381 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13774 : Bounds (-560782969 / 1000000000) (-70097871 / 125000000) (Real.log (285381 / 500000)) := by
  have h := reflection_log_13774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13775_neg : (359125139 / 1000000000) ≤ -Real.log (250000 / 358019) ∧
    -Real.log (250000 / 358019) ≤ (17956257 / 50000000) := by
  have h := checkLog_sound (w := (108019 / 608019)) (n := 12)
    (lo := (359125139 / 1000000000)) (hi := (17956257 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358019 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358019 / 250000) = 1/(250000 / 358019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13775 : Bounds (359125139 / 1000000000) (17956257 / 50000000) (Real.log (358019 / 250000)) := by
  have h := reflection_log_13775_neg
  have he : Real.log (358019 / 250000) = -Real.log (250000 / 358019) := by
    rw [show ((358019 / 250000) : ℝ) = ((250000 / 358019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13776_neg : (70720959 / 125000000) ≤ -Real.log (141981 / 250000) ∧
    -Real.log (141981 / 250000) ≤ (565767673 / 1000000000) := by
  have h := checkLog_sound (w := (108019 / 391981)) (n := 12)
    (lo := (70720959 / 125000000)) (hi := (565767673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 141981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 141981) = 1/(141981 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13776 : Bounds (-565767673 / 1000000000) (-70720959 / 125000000) (Real.log (141981 / 250000)) := by
  have h := reflection_log_13776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13777_neg : (51660633 / 250000000) ≤ -Real.log (50831895639 / 62500000000) ∧
    -Real.log (50831895639 / 62500000000) ≤ (206642533 / 1000000000) := by
  have h := checkLog_sound (w := (11668104361 / 113331895639)) (n := 12)
    (lo := (51660633 / 250000000)) (hi := (206642533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 50831895639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 50831895639) = 1/(50831895639 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13777 : Bounds (-206642533 / 1000000000) (-51660633 / 250000000) (Real.log (50831895639 / 62500000000)) := by
  have h := reflection_log_13777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13778_neg : (203641533 / 1000000000) ≤ -Real.log (203938684839 / 250000000000) ∧
    -Real.log (203938684839 / 250000000000) ≤ (101820767 / 500000000) := by
  have h := checkLog_sound (w := (46061315161 / 453938684839)) (n := 12)
    (lo := (203641533 / 1000000000)) (hi := (101820767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 203938684839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 203938684839) = 1/(203938684839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13778 : Bounds (-101820767 / 500000000) (-203641533 / 1000000000) (Real.log (203938684839 / 250000000000)) := by
  have h := reflection_log_13778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13779_neg : (917924403 / 1000000000) ≤ -Real.log (125000000000 / 313010939761) ∧
    -Real.log (125000000000 / 313010939761) ≤ (183584881 / 200000000) := by
  have h := checkLog_sound (w := (63010939761 / 563010939761)) (n := 12)
    (lo := (224777223 / 1000000000)) (hi := (28097153 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313010939761 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(313010939761 / 250000000000) = 1/(125000000000 / 313010939761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13779 : Bounds (917924403 / 1000000000) (183584881 / 200000000) (Real.log (313010939761 / 125000000000)) := by
  have h := reflection_log_13779_neg
  have he : Real.log (313010939761 / 125000000000) = -Real.log (125000000000 / 313010939761) := by
    rw [show ((313010939761 / 125000000000) : ℝ) = ((125000000000 / 313010939761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13780_neg : (924892811 / 1000000000) ≤ -Real.log (250000000000 / 630399490073) ∧
    -Real.log (250000000000 / 630399490073) ≤ (924892813 / 1000000000) := by
  have h := checkLog_sound (w := (130399490073 / 1130399490073)) (n := 12)
    (lo := (231745631 / 1000000000)) (hi := (7242051 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630399490073 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(630399490073 / 500000000000) = 1/(250000000000 / 630399490073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13780 : Bounds (924892811 / 1000000000) (924892813 / 1000000000) (Real.log (630399490073 / 250000000000)) := by
  have h := reflection_log_13780_neg
  have he : Real.log (630399490073 / 250000000000) = -Real.log (250000000000 / 630399490073) := by
    rw [show ((630399490073 / 250000000000) : ℝ) = ((250000000000 / 630399490073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13781_neg : (399434711 / 200000000) ≤ -Real.log (50000000000 / 368410041841) ∧
    -Real.log (50000000000 / 368410041841) ≤ (998586779 / 500000000) := by
  have h := checkLog_sound (w := (168410041841 / 568410041841)) (n := 12)
    (lo := (122175839 / 200000000)) (hi := (152719799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368410041841 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(368410041841 / 200000000000) = 1/(50000000000 / 368410041841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13781 : Bounds (399434711 / 200000000) (998586779 / 500000000) (Real.log (368410041841 / 50000000000)) := by
  have h := reflection_log_13781_neg
  have he : Real.log (368410041841 / 50000000000) = -Real.log (50000000000 / 368410041841) := by
    rw [show ((368410041841 / 50000000000) : ℝ) = ((50000000000 / 368410041841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13782_neg : (201150743 / 100000000) ≤ -Real.log (250000000000 / 1868644067797) ∧
    -Real.log (250000000000 / 1868644067797) ≤ (2011507433 / 1000000000) := by
  have h := checkLog_sound (w := (868644067797 / 2868644067797)) (n := 12)
    (lo := (62521307 / 100000000)) (hi := (625213071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1868644067797 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1868644067797 / 1000000000000) = 1/(250000000000 / 1868644067797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13782 : Bounds (201150743 / 100000000) (2011507433 / 1000000000) (Real.log (1868644067797 / 250000000000)) := by
  have h := reflection_log_13782_neg
  have he : Real.log (1868644067797 / 250000000000) = -Real.log (250000000000 / 1868644067797) := by
    rw [show ((1868644067797 / 250000000000) : ℝ) = ((250000000000 / 1868644067797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13783_neg : (569283193 / 1000000000) ≤ -Real.log (1000 / 1767) ∧
    -Real.log (1000 / 1767) ≤ (284641597 / 500000000) := by
  have h := checkLog_sound (w := (767 / 2767)) (n := 12)
    (lo := (569283193 / 1000000000)) (hi := (284641597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1767 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1767 / 1000) = 1/(1000 / 1767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13783 : Bounds (569283193 / 1000000000) (284641597 / 500000000) (Real.log (1767 / 1000)) := by
  have h := reflection_log_13783_neg
  have he : Real.log (1767 / 1000) = -Real.log (1000 / 1767) := by
    rw [show ((1767 / 1000) : ℝ) = ((1000 / 1767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13784_neg : (182089603 / 125000000) ≤ -Real.log (233 / 1000) ∧
    -Real.log (233 / 1000) ≤ (1456716827 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 483)) (n := 12)
    (lo := (1100351 / 15625000)) (hi := (14084493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 233) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 233) = 1/(233 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13784 : Bounds (-1456716827 / 1000000000) (-182089603 / 125000000) (Real.log (233 / 1000)) := by
  have h := reflection_log_13784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13785_neg : (383353 / 500000000) ≤ -Real.log (1000000 / 1000767) ∧
    -Real.log (1000000 / 1000767) ≤ (766707 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 2000767)) (n := 12)
    (lo := (383353 / 500000000)) (hi := (766707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000767 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000767 / 1000000) = 1/(1000000 / 1000767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13785 : Bounds (383353 / 500000000) (766707 / 1000000000) (Real.log (1000767 / 1000000)) := by
  have h := reflection_log_13785_neg
  have he : Real.log (1000767 / 1000000) = -Real.log (1000000 / 1000767) := by
    rw [show ((1000767 / 1000000) : ℝ) = ((1000000 / 1000767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13786_neg : (383647 / 500000000) ≤ -Real.log (999233 / 1000000) ∧
    -Real.log (999233 / 1000000) ≤ (153459 / 200000000) := by
  have h := checkLog_sound (w := (767 / 1999233)) (n := 12)
    (lo := (383647 / 500000000)) (hi := (153459 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999233) = 1/(999233 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13786 : Bounds (-153459 / 200000000) (-383647 / 500000000) (Real.log (999233 / 1000000)) := by
  have h := reflection_log_13786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13787_neg : (358672547 / 1000000000) ≤ -Real.log (250000 / 357857) ∧
    -Real.log (250000 / 357857) ≤ (89668137 / 250000000) := by
  have h := checkLog_sound (w := (107857 / 607857)) (n := 12)
    (lo := (358672547 / 1000000000)) (hi := (89668137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357857 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357857 / 250000) = 1/(250000 / 357857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13787 : Bounds (358672547 / 1000000000) (89668137 / 250000000) (Real.log (357857 / 250000)) := by
  have h := reflection_log_13787_neg
  have he : Real.log (357857 / 250000) = -Real.log (250000 / 357857) := by
    rw [show ((357857 / 250000) : ℝ) = ((250000 / 357857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13788_neg : (141156831 / 250000000) ≤ -Real.log (142143 / 250000) ∧
    -Real.log (142143 / 250000) ≤ (22585093 / 40000000) := by
  have h := checkLog_sound (w := (107857 / 392143)) (n := 12)
    (lo := (141156831 / 250000000)) (hi := (22585093 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 142143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 142143) = 1/(142143 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13788 : Bounds (-22585093 / 40000000) (-141156831 / 250000000) (Real.log (142143 / 250000)) := by
  have h := reflection_log_13788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13789_neg : (11270631 / 31250000) ≤ -Real.log (250000 / 358569) ∧
    -Real.log (250000 / 358569) ≤ (360660193 / 1000000000) := by
  have h := checkLog_sound (w := (108569 / 608569)) (n := 12)
    (lo := (11270631 / 31250000)) (hi := (360660193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358569 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358569 / 250000) = 1/(250000 / 358569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13789 : Bounds (11270631 / 31250000) (360660193 / 1000000000) (Real.log (358569 / 250000)) := by
  have h := reflection_log_13789_neg
  have he : Real.log (358569 / 250000) = -Real.log (250000 / 358569) := by
    rw [show ((358569 / 250000) : ℝ) = ((250000 / 358569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13790_neg : (71206119 / 125000000) ≤ -Real.log (141431 / 250000) ∧
    -Real.log (141431 / 250000) ≤ (569648953 / 1000000000) := by
  have h := checkLog_sound (w := (108569 / 391431)) (n := 12)
    (lo := (71206119 / 125000000)) (hi := (569648953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 141431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 141431) = 1/(141431 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13790 : Bounds (-569648953 / 1000000000) (-71206119 / 125000000) (Real.log (141431 / 250000)) := by
  have h := reflection_log_13790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13791_neg : (208988759 / 1000000000) ≤ -Real.log (50712772239 / 62500000000) ∧
    -Real.log (50712772239 / 62500000000) ≤ (5224719 / 25000000) := by
  have h := checkLog_sound (w := (11787227761 / 113212772239)) (n := 12)
    (lo := (208988759 / 1000000000)) (hi := (5224719 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 50712772239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 50712772239) = 1/(50712772239 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13791 : Bounds (-5224719 / 25000000) (-208988759 / 1000000000) (Real.log (50712772239 / 62500000000)) := by
  have h := reflection_log_13791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13792_neg : (205954777 / 1000000000) ≤ -Real.log (50866867551 / 62500000000) ∧
    -Real.log (50866867551 / 62500000000) ≤ (102977389 / 500000000) := by
  have h := checkLog_sound (w := (11633132449 / 113366867551)) (n := 12)
    (lo := (205954777 / 1000000000)) (hi := (102977389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 50866867551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 50866867551) = 1/(50866867551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13792 : Bounds (-102977389 / 500000000) (-205954777 / 1000000000) (Real.log (50866867551 / 62500000000)) := by
  have h := reflection_log_13792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13793_neg : (923299871 / 1000000000) ≤ -Real.log (250000000000 / 629396101109) ∧
    -Real.log (250000000000 / 629396101109) ≤ (923299873 / 1000000000) := by
  have h := checkLog_sound (w := (129396101109 / 1129396101109)) (n := 12)
    (lo := (230152691 / 1000000000)) (hi := (57538173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629396101109 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(629396101109 / 500000000000) = 1/(250000000000 / 629396101109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13793 : Bounds (923299871 / 1000000000) (923299873 / 1000000000) (Real.log (629396101109 / 250000000000)) := by
  have h := reflection_log_13793_neg
  have he : Real.log (629396101109 / 250000000000) = -Real.log (250000000000 / 629396101109) := by
    rw [show ((629396101109 / 250000000000) : ℝ) = ((250000000000 / 629396101109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13794_neg : (930309143 / 1000000000) ≤ -Real.log (500000000000 / 1267646414153) ∧
    -Real.log (500000000000 / 1267646414153) ≤ (186061829 / 200000000) := by
  have h := checkLog_sound (w := (267646414153 / 2267646414153)) (n := 12)
    (lo := (237161963 / 1000000000)) (hi := (59290491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267646414153 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1267646414153 / 1000000000000) = 1/(500000000000 / 1267646414153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13794 : Bounds (930309143 / 1000000000) (186061829 / 200000000) (Real.log (1267646414153 / 500000000000)) := by
  have h := reflection_log_13794_neg
  have he : Real.log (1267646414153 / 500000000000) = -Real.log (500000000000 / 1267646414153) := by
    rw [show ((1267646414153 / 500000000000) : ℝ) = ((500000000000 / 1267646414153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13795_neg : (201150743 / 100000000) ≤ -Real.log (500000000000 / 3737288135593) ∧
    -Real.log (500000000000 / 3737288135593) ≤ (2011507433 / 1000000000) := by
  have h := checkLog_sound (w := (1737288135593 / 5737288135593)) (n := 12)
    (lo := (62521307 / 100000000)) (hi := (625213071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3737288135593 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3737288135593 / 2000000000000) = 1/(500000000000 / 3737288135593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13795 : Bounds (201150743 / 100000000) (2011507433 / 1000000000) (Real.log (3737288135593 / 500000000000)) := by
  have h := reflection_log_13795_neg
  have he : Real.log (3737288135593 / 500000000000) = -Real.log (500000000000 / 3737288135593) := by
    rw [show ((3737288135593 / 500000000000) : ℝ) = ((500000000000 / 3737288135593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13796_neg : (2026000017 / 1000000000) ≤ -Real.log (500000000000 / 3791845493563) ∧
    -Real.log (500000000000 / 3791845493563) ≤ (101300001 / 50000000) := by
  have h := checkLog_sound (w := (1791845493563 / 5791845493563)) (n := 12)
    (lo := (639705657 / 1000000000)) (hi := (319852829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3791845493563 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3791845493563 / 2000000000000) = 1/(500000000000 / 3791845493563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13796 : Bounds (2026000017 / 1000000000) (101300001 / 50000000) (Real.log (3791845493563 / 500000000000)) := by
  have h := reflection_log_13796_neg
  have he : Real.log (3791845493563 / 500000000000) = -Real.log (500000000000 / 3791845493563) := by
    rw [show ((3791845493563 / 500000000000) : ℝ) = ((500000000000 / 3791845493563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13797_neg : (285489773 / 500000000) ≤ -Real.log (100 / 177) ∧
    -Real.log (100 / 177) ≤ (570979547 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 277)) (n := 12)
    (lo := (285489773 / 500000000)) (hi := (570979547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177 / 100) = 1/(100 / 177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13797 : Bounds (285489773 / 500000000) (570979547 / 1000000000) (Real.log (177 / 100)) := by
  have h := reflection_log_13797_neg
  have he : Real.log (177 / 100) = -Real.log (100 / 177) := by
    rw [show ((177 / 100) : ℝ) = ((100 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13798_neg : (22963687 / 15625000) ≤ -Real.log (23 / 100) ∧
    -Real.log (23 / 100) ≤ (1469675971 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 24)) (n := 12)
    (lo := (10422701 / 125000000)) (hi := (83381609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 23) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 23) = 1/(23 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13798 : Bounds (-1469675971 / 1000000000) (-22963687 / 15625000) (Real.log (23 / 100)) := by
  have h := reflection_log_13798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13799_neg : (769703 / 1000000000) ≤ -Real.log (100000 / 100077) ∧
    -Real.log (100000 / 100077) ≤ (96213 / 125000000) := by
  have h := checkLog_sound (w := (77 / 200077)) (n := 12)
    (lo := (769703 / 1000000000)) (hi := (96213 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100077 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100077 / 100000) = 1/(100000 / 100077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13799 : Bounds (769703 / 1000000000) (96213 / 125000000) (Real.log (100077 / 100000)) := by
  have h := reflection_log_13799_neg
  have he : Real.log (100077 / 100000) = -Real.log (100000 / 100077) := by
    rw [show ((100077 / 100000) : ℝ) = ((100000 / 100077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13800_neg : (96287 / 125000000) ≤ -Real.log (99923 / 100000) ∧
    -Real.log (99923 / 100000) ≤ (770297 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 199923)) (n := 12)
    (lo := (96287 / 125000000)) (hi := (770297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99923) = 1/(99923 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13800 : Bounds (-770297 / 1000000000) (-96287 / 125000000) (Real.log (99923 / 100000)) := by
  have h := reflection_log_13800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13801_neg : (90051899 / 250000000) ≤ -Real.log (1000000 / 1433627) ∧
    -Real.log (1000000 / 1433627) ≤ (360207597 / 1000000000) := by
  have h := checkLog_sound (w := (433627 / 2433627)) (n := 12)
    (lo := (90051899 / 250000000)) (hi := (360207597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1433627 / 1000000) = 1/(1000000 / 1433627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13801 : Bounds (90051899 / 250000000) (360207597 / 1000000000) (Real.log (1433627 / 1000000)) := by
  have h := reflection_log_13801_neg
  have he : Real.log (1433627 / 1000000) = -Real.log (1000000 / 1433627) := by
    rw [show ((1433627 / 1000000) : ℝ) = ((1000000 / 1433627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13802_neg : (568502407 / 1000000000) ≤ -Real.log (566373 / 1000000) ∧
    -Real.log (566373 / 1000000) ≤ (71062801 / 125000000) := by
  have h := checkLog_sound (w := (433627 / 1566373)) (n := 12)
    (lo := (568502407 / 1000000000)) (hi := (71062801 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 566373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 566373) = 1/(566373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13802 : Bounds (-71062801 / 125000000) (-568502407 / 1000000000) (Real.log (566373 / 1000000)) := by
  have h := reflection_log_13802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13803_neg : (362199157 / 1000000000) ≤ -Real.log (200000 / 287297) ∧
    -Real.log (200000 / 287297) ≤ (181099579 / 500000000) := by
  have h := checkLog_sound (w := (87297 / 487297)) (n := 12)
    (lo := (362199157 / 1000000000)) (hi := (181099579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287297 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287297 / 200000) = 1/(200000 / 287297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13803 : Bounds (362199157 / 1000000000) (181099579 / 500000000) (Real.log (287297 / 200000)) := by
  have h := reflection_log_13803_neg
  have he : Real.log (287297 / 200000) = -Real.log (200000 / 287297) := by
    rw [show ((287297 / 200000) : ℝ) = ((200000 / 287297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13804_neg : (286780663 / 500000000) ≤ -Real.log (112703 / 200000) ∧
    -Real.log (112703 / 200000) ≤ (573561327 / 1000000000) := by
  have h := checkLog_sound (w := (87297 / 312703)) (n := 12)
    (lo := (286780663 / 500000000)) (hi := (573561327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 112703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 112703) = 1/(112703 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13804 : Bounds (-573561327 / 1000000000) (-286780663 / 500000000) (Real.log (112703 / 200000)) := by
  have h := reflection_log_13804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13805_neg : (211362169 / 1000000000) ≤ -Real.log (32379233791 / 40000000000) ∧
    -Real.log (32379233791 / 40000000000) ≤ (21136217 / 100000000) := by
  have h := checkLog_sound (w := (7620766209 / 72379233791)) (n := 12)
    (lo := (211362169 / 1000000000)) (hi := (21136217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 32379233791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 32379233791) = 1/(32379233791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13805 : Bounds (-21136217 / 100000000) (-211362169 / 1000000000) (Real.log (32379233791 / 40000000000)) := by
  have h := reflection_log_13805_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13806_neg : (20829481 / 100000000) ≤ -Real.log (811967624871 / 1000000000000) ∧
    -Real.log (811967624871 / 1000000000000) ≤ (208294811 / 1000000000) := by
  have h := checkLog_sound (w := (188032375129 / 1811967624871)) (n := 12)
    (lo := (20829481 / 100000000)) (hi := (208294811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 811967624871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 811967624871) = 1/(811967624871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13806 : Bounds (-208294811 / 1000000000) (-20829481 / 100000000) (Real.log (811967624871 / 1000000000000)) := by
  have h := reflection_log_13806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13807_neg : (928710003 / 1000000000) ≤ -Real.log (500000000000 / 1265620889413) ∧
    -Real.log (500000000000 / 1265620889413) ≤ (185742001 / 200000000) := by
  have h := checkLog_sound (w := (265620889413 / 2265620889413)) (n := 12)
    (lo := (235562823 / 1000000000)) (hi := (29445353 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265620889413 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1265620889413 / 1000000000000) = 1/(500000000000 / 1265620889413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13807 : Bounds (928710003 / 1000000000) (185742001 / 200000000) (Real.log (1265620889413 / 500000000000)) := by
  have h := reflection_log_13807_neg
  have he : Real.log (1265620889413 / 500000000000) = -Real.log (500000000000 / 1265620889413) := by
    rw [show ((1265620889413 / 500000000000) : ℝ) = ((500000000000 / 1265620889413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13808_neg : (935760483 / 1000000000) ≤ -Real.log (500000000000 / 1274575654597) ∧
    -Real.log (500000000000 / 1274575654597) ≤ (187152097 / 200000000) := by
  have h := checkLog_sound (w := (274575654597 / 2274575654597)) (n := 12)
    (lo := (242613303 / 1000000000)) (hi := (30326663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274575654597 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1274575654597 / 1000000000000) = 1/(500000000000 / 1274575654597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13808 : Bounds (935760483 / 1000000000) (187152097 / 200000000) (Real.log (1274575654597 / 500000000000)) := by
  have h := reflection_log_13808_neg
  have he : Real.log (1274575654597 / 500000000000) = -Real.log (500000000000 / 1274575654597) := by
    rw [show ((1274575654597 / 500000000000) : ℝ) = ((500000000000 / 1274575654597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13809_neg : (2026000017 / 1000000000) ≤ -Real.log (250000000000 / 1895922746781) ∧
    -Real.log (250000000000 / 1895922746781) ≤ (101300001 / 50000000) := by
  have h := checkLog_sound (w := (895922746781 / 2895922746781)) (n := 12)
    (lo := (639705657 / 1000000000)) (hi := (319852829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1895922746781 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1895922746781 / 1000000000000) = 1/(250000000000 / 1895922746781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13809 : Bounds (2026000017 / 1000000000) (101300001 / 50000000) (Real.log (1895922746781 / 250000000000)) := by
  have h := reflection_log_13809_neg
  have he : Real.log (1895922746781 / 250000000000) = -Real.log (250000000000 / 1895922746781) := by
    rw [show ((1895922746781 / 250000000000) : ℝ) = ((250000000000 / 1895922746781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13810_neg : (408131103 / 200000000) ≤ -Real.log (500000000000 / 3847826086957) ∧
    -Real.log (500000000000 / 3847826086957) ≤ (1020327759 / 500000000) := by
  have h := checkLog_sound (w := (1847826086957 / 5847826086957)) (n := 12)
    (lo := (130872231 / 200000000)) (hi := (163590289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3847826086957 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3847826086957 / 2000000000000) = 1/(500000000000 / 3847826086957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13810 : Bounds (408131103 / 200000000) (1020327759 / 500000000) (Real.log (3847826086957 / 500000000000)) := by
  have h := reflection_log_13810_neg
  have he : Real.log (3847826086957 / 500000000000) = -Real.log (500000000000 / 3847826086957) := by
    rw [show ((3847826086957 / 500000000000) : ℝ) = ((500000000000 / 3847826086957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13811_neg : (572673027 / 1000000000) ≤ -Real.log (1000 / 1773) ∧
    -Real.log (1000 / 1773) ≤ (143168257 / 250000000) := by
  have h := checkLog_sound (w := (773 / 2773)) (n := 12)
    (lo := (572673027 / 1000000000)) (hi := (143168257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1773 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1773 / 1000) = 1/(1000 / 1773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13811 : Bounds (572673027 / 1000000000) (143168257 / 250000000) (Real.log (1773 / 1000)) := by
  have h := reflection_log_13811_neg
  have he : Real.log (1773 / 1000) = -Real.log (1000 / 1773) := by
    rw [show ((1773 / 1000) : ℝ) = ((1000 / 1773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13812_neg : (74140263 / 50000000) ≤ -Real.log (227 / 1000) ∧
    -Real.log (227 / 1000) ≤ (1482805263 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 477)) (n := 12)
    (lo := (965109 / 10000000)) (hi := (96510901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 227) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 227) = 1/(227 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13812 : Bounds (-1482805263 / 1000000000) (-74140263 / 50000000) (Real.log (227 / 1000)) := by
  have h := reflection_log_13812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13813_neg : (772701 / 1000000000) ≤ -Real.log (1000000 / 1000773) ∧
    -Real.log (1000000 / 1000773) ≤ (386351 / 500000000) := by
  have h := checkLog_sound (w := (773 / 2000773)) (n := 12)
    (lo := (772701 / 1000000000)) (hi := (386351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000773 / 1000000) = 1/(1000000 / 1000773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13813 : Bounds (772701 / 1000000000) (386351 / 500000000) (Real.log (1000773 / 1000000)) := by
  have h := reflection_log_13813_neg
  have he : Real.log (1000773 / 1000000) = -Real.log (1000000 / 1000773) := by
    rw [show ((1000773 / 1000000) : ℝ) = ((1000000 / 1000773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13814_neg : (386649 / 500000000) ≤ -Real.log (999227 / 1000000) ∧
    -Real.log (999227 / 1000000) ≤ (773299 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 1999227)) (n := 12)
    (lo := (386649 / 500000000)) (hi := (773299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999227) = 1/(999227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13814 : Bounds (-773299 / 1000000000) (-386649 / 500000000) (Real.log (999227 / 1000000)) := by
  have h := reflection_log_13814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13815_neg : (72349173 / 200000000) ≤ -Real.log (500000 / 717917) ∧
    -Real.log (500000 / 717917) ≤ (180872933 / 500000000) := by
  have h := checkLog_sound (w := (217917 / 1217917)) (n := 12)
    (lo := (72349173 / 200000000)) (hi := (180872933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717917 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717917 / 500000) = 1/(500000 / 717917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13815 : Bounds (72349173 / 200000000) (180872933 / 500000000) (Real.log (717917 / 500000)) := by
  have h := reflection_log_13815_neg
  have he : Real.log (717917 / 500000) = -Real.log (500000 / 717917) := by
    rw [show ((717917 / 500000) : ℝ) = ((500000 / 717917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13816_neg : (71550843 / 125000000) ≤ -Real.log (282083 / 500000) ∧
    -Real.log (282083 / 500000) ≤ (114481349 / 200000000) := by
  have h := checkLog_sound (w := (217917 / 782083)) (n := 12)
    (lo := (71550843 / 125000000)) (hi := (114481349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 282083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 282083) = 1/(282083 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13816 : Bounds (-114481349 / 200000000) (-71550843 / 125000000) (Real.log (282083 / 500000)) := by
  have h := reflection_log_13816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13817_neg : (181870659 / 500000000) ≤ -Real.log (500000 / 719351) ∧
    -Real.log (500000 / 719351) ≤ (363741319 / 1000000000) := by
  have h := checkLog_sound (w := (219351 / 1219351)) (n := 12)
    (lo := (181870659 / 500000000)) (hi := (363741319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719351 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719351 / 500000) = 1/(500000 / 719351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13817 : Bounds (181870659 / 500000000) (363741319 / 1000000000) (Real.log (719351 / 500000)) := by
  have h := reflection_log_13817_neg
  have he : Real.log (719351 / 500000) = -Real.log (500000 / 719351) := by
    rw [show ((719351 / 500000) : ℝ) = ((500000 / 719351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13818_neg : (14437583 / 25000000) ≤ -Real.log (280649 / 500000) ∧
    -Real.log (280649 / 500000) ≤ (577503321 / 1000000000) := by
  have h := checkLog_sound (w := (219351 / 780649)) (n := 12)
    (lo := (14437583 / 25000000)) (hi := (577503321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 280649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 280649) = 1/(280649 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13818 : Bounds (-577503321 / 1000000000) (-14437583 / 25000000) (Real.log (280649 / 500000)) := by
  have h := reflection_log_13818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13819_neg : (213762001 / 1000000000) ≤ -Real.log (201885138799 / 250000000000) ∧
    -Real.log (201885138799 / 250000000000) ≤ (106881001 / 500000000) := by
  have h := checkLog_sound (w := (48114861201 / 451885138799)) (n := 12)
    (lo := (213762001 / 1000000000)) (hi := (106881001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 201885138799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 201885138799) = 1/(201885138799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13819 : Bounds (-106881001 / 500000000) (-213762001 / 1000000000) (Real.log (201885138799 / 250000000000)) := by
  have h := reflection_log_13819_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13820_neg : (210660879 / 1000000000) ≤ -Real.log (202512181111 / 250000000000) ∧
    -Real.log (202512181111 / 250000000000) ≤ (2633261 / 12500000) := by
  have h := checkLog_sound (w := (47487818889 / 452512181111)) (n := 12)
    (lo := (210660879 / 1000000000)) (hi := (2633261 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 202512181111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 202512181111) = 1/(202512181111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13820 : Bounds (-2633261 / 12500000) (-210660879 / 1000000000) (Real.log (202512181111 / 250000000000)) := by
  have h := reflection_log_13820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13821_neg : (934152609 / 1000000000) ≤ -Real.log (500000000000 / 1272527943903) ∧
    -Real.log (500000000000 / 1272527943903) ≤ (934152611 / 1000000000) := by
  have h := checkLog_sound (w := (272527943903 / 2272527943903)) (n := 12)
    (lo := (241005429 / 1000000000)) (hi := (24100543 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1272527943903 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1272527943903 / 1000000000000) = 1/(500000000000 / 1272527943903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13821 : Bounds (934152609 / 1000000000) (934152611 / 1000000000) (Real.log (1272527943903 / 500000000000)) := by
  have h := reflection_log_13821_neg
  have he : Real.log (1272527943903 / 500000000000) = -Real.log (500000000000 / 1272527943903) := by
    rw [show ((1272527943903 / 500000000000) : ℝ) = ((500000000000 / 1272527943903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13822_neg : (941244637 / 1000000000) ≤ -Real.log (500000000000 / 1281584826599) ∧
    -Real.log (500000000000 / 1281584826599) ≤ (941244639 / 1000000000) := by
  have h := checkLog_sound (w := (281584826599 / 2281584826599)) (n := 12)
    (lo := (248097457 / 1000000000)) (hi := (124048729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281584826599 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1281584826599 / 1000000000000) = 1/(500000000000 / 1281584826599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13822 : Bounds (941244637 / 1000000000) (941244639 / 1000000000) (Real.log (1281584826599 / 500000000000)) := by
  have h := reflection_log_13822_neg
  have he : Real.log (1281584826599 / 500000000000) = -Real.log (500000000000 / 1281584826599) := by
    rw [show ((1281584826599 / 500000000000) : ℝ) = ((500000000000 / 1281584826599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13823_neg : (408131103 / 200000000) ≤ -Real.log (125000000000 / 961956521739) ∧
    -Real.log (125000000000 / 961956521739) ≤ (1020327759 / 500000000) := by
  have h := checkLog_sound (w := (461956521739 / 1461956521739)) (n := 12)
    (lo := (130872231 / 200000000)) (hi := (163590289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961956521739 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(961956521739 / 500000000000) = 1/(125000000000 / 961956521739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13823 : Bounds (408131103 / 200000000) (1020327759 / 500000000) (Real.log (961956521739 / 125000000000)) := by
  have h := reflection_log_13823_neg
  have he : Real.log (961956521739 / 125000000000) = -Real.log (125000000000 / 961956521739) := by
    rw [show ((961956521739 / 125000000000) : ℝ) = ((125000000000 / 961956521739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

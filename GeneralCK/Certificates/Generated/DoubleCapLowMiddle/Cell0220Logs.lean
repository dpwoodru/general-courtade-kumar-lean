import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0220
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

theorem reflection_log_1_neg : (524173641 / 1000000000) ≤ -Real.log (640 / 1081) ∧
    -Real.log (640 / 1081) ≤ (262086821 / 500000000) := by
  have h := checkLog_sound (w := (441 / 1721)) (n := 12)
    (lo := (524173641 / 1000000000)) (hi := (262086821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081 / 640) = 1/(640 / 1081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (524173641 / 1000000000) (262086821 / 500000000) (Real.log (1081 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1081 / 640) = -Real.log (640 / 1081) := by
    rw [show ((1081 / 640) : ℝ) = ((640 / 1081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1168163351 / 1000000000) ≤ -Real.log (199 / 640) ∧
    -Real.log (199 / 640) ≤ (1168163353 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 199) = 1/(199 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1168163353 / 1000000000) (-1168163351 / 1000000000) (Real.log (199 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65081523 / 125000000) ≤ -Real.log (1600 / 2693) ∧
    -Real.log (1600 / 2693) ≤ (104130437 / 200000000) := by
  have h := checkLog_sound (w := (1093 / 4293)) (n := 12)
    (lo := (65081523 / 125000000)) (hi := (104130437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2693 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2693 / 1600) = 1/(1600 / 2693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65081523 / 125000000) (104130437 / 200000000) (Real.log (2693 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2693 / 1600) = -Real.log (1600 / 2693) := by
    rw [show ((2693 / 1600) : ℝ) = ((1600 / 2693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (35913997 / 31250000) ≤ -Real.log (507 / 1600) ∧
    -Real.log (507 / 1600) ≤ (574623953 / 500000000) := by
  have h := checkLog_sound (w := (293 / 1307)) (n := 12)
    (lo := (114025181 / 250000000)) (hi := (18244029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 507) = 1/(507 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-574623953 / 500000000) (-35913997 / 31250000) (Real.log (507 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (320723879 / 1000000000) ≤ -Real.log (320 / 441) ∧
    -Real.log (320 / 441) ≤ (8018097 / 25000000) := by
  have h := checkLog_sound (w := (121 / 761)) (n := 12)
    (lo := (320723879 / 1000000000)) (hi := (8018097 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441 / 320) = 1/(320 / 441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (320723879 / 1000000000) (8018097 / 25000000) (Real.log (441 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (441 / 320) = -Real.log (320 / 441) := by
    rw [show ((441 / 320) : ℝ) = ((320 / 441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (475016171 / 1000000000) ≤ -Real.log (199 / 320) ∧
    -Real.log (199 / 320) ≤ (118754043 / 250000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 199) = 1/(199 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-118754043 / 250000000) (-475016171 / 1000000000) (Real.log (199 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (487609 / 1562500) ≤ -Real.log (800 / 1093) ∧
    -Real.log (800 / 1093) ≤ (312069761 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 1893)) (n := 12)
    (lo := (487609 / 1562500)) (hi := (312069761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093 / 800) = 1/(800 / 1093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (487609 / 1562500) (312069761 / 1000000000) (Real.log (1093 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1093 / 800) = -Real.log (800 / 1093) := by
    rw [show ((1093 / 800) : ℝ) = ((800 / 1093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (114025181 / 250000000) ≤ -Real.log (507 / 800) ∧
    -Real.log (507 / 800) ≤ (18244029 / 40000000) := by
  have h := checkLog_sound (w := (293 / 1307)) (n := 12)
    (lo := (114025181 / 250000000)) (hi := (18244029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 507) = 1/(507 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-18244029 / 40000000) (-114025181 / 250000000) (Real.log (507 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (594162959 / 1000000000) ≤ -Real.log (500000 / 905757) ∧
    -Real.log (500000 / 905757) ≤ (7427037 / 12500000) := by
  have h := checkLog_sound (w := (405757 / 1405757)) (n := 12)
    (lo := (594162959 / 1000000000)) (hi := (7427037 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((905757 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(905757 / 500000) = 1/(500000 / 905757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (594162959 / 1000000000) (7427037 / 12500000) (Real.log (905757 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (905757 / 500000) = -Real.log (500000 / 905757) := by
    rw [show ((905757 / 500000) : ℝ) = ((500000 / 905757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (208591443 / 125000000) ≤ -Real.log (94243 / 500000) ∧
    -Real.log (94243 / 500000) ≤ (1668731547 / 1000000000) := by
  have h := checkLog_sound (w := (30757 / 219243)) (n := 12)
    (lo := (4413081 / 15625000)) (hi := (56487437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94243) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 94243) = 1/(94243 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1668731547 / 1000000000) (-208591443 / 125000000) (Real.log (94243 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (119058463 / 200000000) ≤ -Real.log (1000000 / 1813561) ∧
    -Real.log (1000000 / 1813561) ≤ (148823079 / 250000000) := by
  have h := checkLog_sound (w := (813561 / 2813561)) (n := 12)
    (lo := (119058463 / 200000000)) (hi := (148823079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1813561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1813561 / 1000000) = 1/(1000000 / 1813561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (119058463 / 200000000) (148823079 / 250000000) (Real.log (1813561 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1813561 / 1000000) = -Real.log (1000000 / 1813561) := by
    rw [show ((1813561 / 1000000) : ℝ) = ((1000000 / 1813561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (167965117 / 100000000) ≤ -Real.log (186439 / 1000000) ∧
    -Real.log (186439 / 1000000) ≤ (1679651173 / 1000000000) := by
  have h := checkLog_sound (w := (63561 / 436439)) (n := 12)
    (lo := (29335681 / 100000000)) (hi := (293356811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186439) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 186439) = 1/(186439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1679651173 / 1000000000) (-167965117 / 100000000) (Real.log (186439 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (572841653 / 1000000000) ≤ -Real.log (1000000 / 1773299) ∧
    -Real.log (1000000 / 1773299) ≤ (286420827 / 500000000) := by
  have h := checkLog_sound (w := (773299 / 2773299)) (n := 12)
    (lo := (572841653 / 1000000000)) (hi := (286420827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1773299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1773299 / 1000000) = 1/(1000000 / 1773299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (572841653 / 1000000000) (286420827 / 500000000) (Real.log (1773299 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1773299 / 1000000) = -Real.log (1000000 / 1773299) := by
    rw [show ((1773299 / 1000000) : ℝ) = ((1000000 / 1773299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1484123309 / 1000000000) ≤ -Real.log (226701 / 1000000) ∧
    -Real.log (226701 / 1000000) ≤ (92757707 / 62500000) := by
  have h := checkLog_sound (w := (23299 / 476701)) (n := 12)
    (lo := (97828949 / 1000000000)) (hi := (1956579 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226701) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 226701) = 1/(226701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-92757707 / 62500000) (-1484123309 / 1000000000) (Real.log (226701 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (574988449 / 1000000000) ≤ -Real.log (100000 / 177711) ∧
    -Real.log (100000 / 177711) ≤ (11499769 / 20000000) := by
  have h := checkLog_sound (w := (77711 / 277711)) (n := 12)
    (lo := (574988449 / 1000000000)) (hi := (11499769 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177711 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177711 / 100000) = 1/(100000 / 177711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (574988449 / 1000000000) (11499769 / 20000000) (Real.log (177711 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (177711 / 100000) = -Real.log (100000 / 177711) := by
    rw [show ((177711 / 100000) : ℝ) = ((100000 / 177711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1501076901 / 1000000000) ≤ -Real.log (22289 / 100000) ∧
    -Real.log (22289 / 100000) ≤ (187634613 / 125000000) := by
  have h := checkLog_sound (w := (2711 / 47289)) (n := 12)
    (lo := (114782541 / 1000000000)) (hi := (57391271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22289) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 22289) = 1/(22289 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-187634613 / 125000000) (-1501076901 / 1000000000) (Real.log (22289 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2262894503 / 1000000000) ≤ -Real.log (500000000000 / 4805433825323) ∧
    -Real.log (500000000000 / 4805433825323) ≤ (2262894507 / 1000000000) := by
  have h := checkLog_sound (w := (805433825323 / 8805433825323)) (n := 12)
    (lo := (183452963 / 1000000000)) (hi := (45863241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4805433825323 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4805433825323 / 4000000000000) = 1/(500000000000 / 4805433825323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2262894503 / 1000000000) (2262894507 / 1000000000) (Real.log (4805433825323 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4805433825323 / 500000000000) = -Real.log (500000000000 / 4805433825323) := by
    rw [show ((4805433825323 / 500000000000) : ℝ) = ((500000000000 / 4805433825323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (454988697 / 200000000) ≤ -Real.log (500000000000 / 4863684636799) ∧
    -Real.log (500000000000 / 4863684636799) ≤ (2274943489 / 1000000000) := by
  have h := checkLog_sound (w := (863684636799 / 8863684636799)) (n := 12)
    (lo := (39100389 / 200000000)) (hi := (97750973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4863684636799 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4863684636799 / 4000000000000) = 1/(500000000000 / 4863684636799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (454988697 / 200000000) (2274943489 / 1000000000) (Real.log (4863684636799 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4863684636799 / 500000000000) = -Real.log (500000000000 / 4863684636799) := by
    rw [show ((4863684636799 / 500000000000) : ℝ) = ((500000000000 / 4863684636799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1028482481 / 500000000) ≤ -Real.log (125000000000 / 977774138623) ∧
    -Real.log (125000000000 / 977774138623) ≤ (411392993 / 200000000) := by
  have h := checkLog_sound (w := (477774138623 / 1477774138623)) (n := 12)
    (lo := (335335301 / 500000000)) (hi := (670670603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977774138623 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(977774138623 / 500000000000) = 1/(125000000000 / 977774138623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1028482481 / 500000000) (411392993 / 200000000) (Real.log (977774138623 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (977774138623 / 125000000000) = -Real.log (125000000000 / 977774138623) := by
    rw [show ((977774138623 / 125000000000) : ℝ) = ((125000000000 / 977774138623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (41521307 / 20000000) ≤ -Real.log (50000000000 / 398651801337) ∧
    -Real.log (50000000000 / 398651801337) ≤ (2076065353 / 1000000000) := by
  have h := checkLog_sound (w := (198651801337 / 598651801337)) (n := 12)
    (lo := (68977099 / 100000000)) (hi := (689770991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398651801337 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(398651801337 / 200000000000) = 1/(50000000000 / 398651801337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (41521307 / 20000000) (2076065353 / 1000000000) (Real.log (398651801337 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (398651801337 / 50000000000) = -Real.log (50000000000 / 398651801337) := by
    rw [show ((398651801337 / 50000000000) : ℝ) = ((50000000000 / 398651801337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0220

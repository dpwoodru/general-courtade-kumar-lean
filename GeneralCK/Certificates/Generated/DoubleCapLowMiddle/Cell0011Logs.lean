import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0011
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

theorem reflection_log_1_neg : (682581303 / 1000000000) ≤ -Real.log (250000000000 / 494744873047) ∧
    -Real.log (250000000000 / 494744873047) ≤ (85322663 / 125000000) := by
  have h := checkLog_sound (w := (244744873047 / 744744873047)) (n := 12)
    (lo := (682581303 / 1000000000)) (hi := (85322663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494744873047 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494744873047 / 250000000000) = 1/(250000000000 / 494744873047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682581303 / 1000000000) (85322663 / 125000000) (Real.log (494744873047 / 250000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (494744873047 / 250000000000) = -Real.log (250000000000 / 494744873047) := by
    rw [show ((494744873047 / 250000000000) : ℝ) = ((250000000000 / 494744873047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (241391047 / 62500000) ≤ -Real.log (5255126953 / 250000000000) ∧
    -Real.log (5255126953 / 250000000000) ≤ (1931128379 / 500000000) := by
  have h := checkLog_sound (w := (2557373047 / 13067626953)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7812500000 / 5255126953) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7812500000 / 5255126953) = 1/(5255126953 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1931128379 / 500000000) (-241391047 / 62500000) (Real.log (5255126953 / 250000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682534423 / 1000000000) ≤ -Real.log (51200 / 101319) ∧
    -Real.log (51200 / 101319) ≤ (85316803 / 125000000) := by
  have h := checkLog_sound (w := (50119 / 152519)) (n := 12)
    (lo := (682534423 / 1000000000)) (hi := (85316803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101319 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101319 / 51200) = 1/(51200 / 101319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682534423 / 1000000000) (85316803 / 125000000) (Real.log (101319 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101319 / 51200) = -Real.log (51200 / 101319) := by
    rw [show ((101319 / 51200) : ℝ) = ((51200 / 101319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (385785299 / 100000000) ≤ -Real.log (1081 / 51200) ∧
    -Real.log (1081 / 51200) ≤ (964463249 / 250000000) := by
  have h := checkLog_sound (w := (519 / 2681)) (n := 12)
    (lo := (39211709 / 100000000)) (hi := (392117091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1081) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1081) = 1/(1081 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-964463249 / 250000000) (-385785299 / 100000000) (Real.log (1081 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167975649 / 250000000) ≤ -Real.log (20480 / 40099) ∧
    -Real.log (20480 / 40099) ≤ (671902597 / 1000000000) := by
  have h := checkLog_sound (w := (19619 / 60579)) (n := 12)
    (lo := (167975649 / 250000000)) (hi := (671902597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40099 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40099 / 20480) = 1/(20480 / 40099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167975649 / 250000000) (671902597 / 1000000000) (Real.log (40099 / 20480)) := by
  have h := reflection_log_5_neg
  have he : Real.log (40099 / 20480) = -Real.log (20480 / 40099) := by
    rw [show ((40099 / 20480) : ℝ) = ((20480 / 40099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (792277393 / 250000000) ≤ -Real.log (861 / 20480) ∧
    -Real.log (861 / 20480) ≤ (3169109577 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2141)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 861) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1280 / 861) = 1/(861 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3169109577 / 1000000000) (-792277393 / 250000000) (Real.log (861 / 20480)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (335903913 / 500000000) ≤ -Real.log (25600 / 50119) ∧
    -Real.log (25600 / 50119) ≤ (671807827 / 1000000000) := by
  have h := checkLog_sound (w := (24519 / 75719)) (n := 12)
    (lo := (335903913 / 500000000)) (hi := (671807827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50119 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50119 / 25600) = 1/(25600 / 50119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (335903913 / 500000000) (671807827 / 1000000000) (Real.log (50119 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (50119 / 25600) = -Real.log (25600 / 50119) := by
    rw [show ((50119 / 25600) : ℝ) = ((25600 / 50119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (316470581 / 100000000) ≤ -Real.log (1081 / 25600) ∧
    -Real.log (1081 / 25600) ≤ (632941163 / 200000000) := by
  have h := checkLog_sound (w := (519 / 2681)) (n := 12)
    (lo := (39211709 / 100000000)) (hi := (392117091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1081) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1081) = 1/(1081 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-632941163 / 200000000) (-316470581 / 100000000) (Real.log (1081 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684145789 / 1000000000) ≤ -Real.log (500000 / 991039) ∧
    -Real.log (500000 / 991039) ≤ (68414579 / 100000000) := by
  have h := checkLog_sound (w := (491039 / 1491039)) (n := 12)
    (lo := (684145789 / 1000000000)) (hi := (68414579 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991039 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991039 / 500000) = 1/(500000 / 991039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684145789 / 1000000000) (68414579 / 100000000) (Real.log (991039 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (991039 / 500000) = -Real.log (500000 / 991039) := by
    rw [show ((991039 / 500000) : ℝ) = ((500000 / 991039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4021726267 / 1000000000) ≤ -Real.log (8961 / 500000) ∧
    -Real.log (8961 / 500000) ≤ (4021726273 / 1000000000) := by
  have h := checkLog_sound (w := (3332 / 12293)) (n := 12)
    (lo := (555990367 / 1000000000)) (hi := (17374699 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8961) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8961) = 1/(8961 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4021726273 / 1000000000) (-4021726267 / 1000000000) (Real.log (8961 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (171046033 / 250000000) ≤ -Real.log (500000 / 991077) ∧
    -Real.log (500000 / 991077) ≤ (684184133 / 1000000000) := by
  have h := checkLog_sound (w := (491077 / 1491077)) (n := 12)
    (lo := (171046033 / 250000000)) (hi := (684184133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991077 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991077 / 500000) = 1/(500000 / 991077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (171046033 / 250000000) (684184133 / 1000000000) (Real.log (991077 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (991077 / 500000) = -Real.log (500000 / 991077) := by
    rw [show ((991077 / 500000) : ℝ) = ((500000 / 991077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2012987941 / 500000000) ≤ -Real.log (8923 / 500000) ∧
    -Real.log (8923 / 500000) ≤ (251623493 / 62500000) := by
  have h := checkLog_sound (w := (3351 / 12274)) (n := 12)
    (lo := (280119991 / 500000000)) (hi := (560239983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8923) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8923) = 1/(8923 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-251623493 / 62500000) (-2012987941 / 500000000) (Real.log (8923 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (85513809 / 125000000) ≤ -Real.log (125000 / 247751) ∧
    -Real.log (125000 / 247751) ≤ (684110473 / 1000000000) := by
  have h := checkLog_sound (w := (122751 / 372751)) (n := 12)
    (lo := (85513809 / 125000000)) (hi := (684110473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247751 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247751 / 125000) = 1/(125000 / 247751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (85513809 / 125000000) (684110473 / 1000000000) (Real.log (247751 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247751 / 125000) = -Real.log (125000 / 247751) := by
    rw [show ((247751 / 125000) : ℝ) = ((125000 / 247751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4017828061 / 1000000000) ≤ -Real.log (2249 / 125000) ∧
    -Real.log (2249 / 125000) ≤ (4017828067 / 1000000000) := by
  have h := checkLog_sound (w := (6629 / 24621)) (n := 12)
    (lo := (552092161 / 1000000000)) (hi := (276046081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8996) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8996) = 1/(2249 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4017828067 / 1000000000) (-4017828061 / 1000000000) (Real.log (2249 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (27365993 / 40000000) ≤ -Real.log (500000 / 991043) ∧
    -Real.log (500000 / 991043) ≤ (342074913 / 500000000) := by
  have h := checkLog_sound (w := (491043 / 1491043)) (n := 12)
    (lo := (27365993 / 40000000)) (hi := (342074913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991043 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991043 / 500000) = 1/(500000 / 991043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (27365993 / 40000000) (342074913 / 500000000) (Real.log (991043 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (991043 / 500000) = -Real.log (500000 / 991043) := by
    rw [show ((991043 / 500000) : ℝ) = ((500000 / 991043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2011086373 / 500000000) ≤ -Real.log (8957 / 500000) ∧
    -Real.log (8957 / 500000) ≤ (251385797 / 62500000) := by
  have h := checkLog_sound (w := (3334 / 12291)) (n := 12)
    (lo := (278218423 / 500000000)) (hi := (556436847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8957) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8957) = 1/(8957 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-251385797 / 62500000) (-2011086373 / 500000000) (Real.log (8957 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (588234007 / 125000000) ≤ -Real.log (500000000000 / 55297344046423) ∧
    -Real.log (500000000000 / 55297344046423) ≤ (4705872063 / 1000000000) := by
  have h := checkLog_sound (w := (23297344046423 / 87297344046423)) (n := 12)
    (lo := (34186811 / 62500000)) (hi := (546988977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55297344046423 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55297344046423 / 32000000000000) = 1/(500000000000 / 55297344046423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (588234007 / 125000000) (4705872063 / 1000000000) (Real.log (55297344046423 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (55297344046423 / 500000000000) = -Real.log (500000000000 / 55297344046423) := by
    rw [show ((55297344046423 / 500000000000) : ℝ) = ((500000000000 / 55297344046423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2355080007 / 500000000) ≤ -Real.log (500000000000 / 55534965818671) ∧
    -Real.log (500000000000 / 55534965818671) ≤ (4710160021 / 1000000000) := by
  have h := checkLog_sound (w := (23534965818671 / 87534965818671)) (n := 12)
    (lo := (275638467 / 500000000)) (hi := (110255387 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55534965818671 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55534965818671 / 32000000000000) = 1/(500000000000 / 55534965818671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2355080007 / 500000000) (4710160021 / 1000000000) (Real.log (55534965818671 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (55534965818671 / 500000000000) = -Real.log (500000000000 / 55534965818671) := by
    rw [show ((55534965818671 / 500000000000) : ℝ) = ((500000000000 / 55534965818671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4701938533 / 1000000000) ≤ -Real.log (125000000000 / 13770064473099) ∧
    -Real.log (125000000000 / 13770064473099) ≤ (235096927 / 50000000) := by
  have h := checkLog_sound (w := (5770064473099 / 21770064473099)) (n := 12)
    (lo := (543055453 / 1000000000)) (hi := (271527727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13770064473099 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(13770064473099 / 8000000000000) = 1/(125000000000 / 13770064473099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4701938533 / 1000000000) (235096927 / 50000000) (Real.log (13770064473099 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13770064473099 / 125000000000) = -Real.log (125000000000 / 13770064473099) := by
    rw [show ((13770064473099 / 125000000000) : ℝ) = ((125000000000 / 13770064473099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4706322571 / 1000000000) ≤ -Real.log (500000000000 / 55322261918053) ∧
    -Real.log (500000000000 / 55322261918053) ≤ (2353161289 / 500000000) := by
  have h := checkLog_sound (w := (23322261918053 / 87322261918053)) (n := 12)
    (lo := (547439491 / 1000000000)) (hi := (136859873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55322261918053 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55322261918053 / 32000000000000) = 1/(500000000000 / 55322261918053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4706322571 / 1000000000) (2353161289 / 500000000) (Real.log (55322261918053 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (55322261918053 / 500000000000) = -Real.log (500000000000 / 55322261918053) := by
    rw [show ((55322261918053 / 500000000000) : ℝ) = ((500000000000 / 55322261918053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0011

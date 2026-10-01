import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0442
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

theorem reflection_log_1_neg : (190103697 / 1000000000) ≤ -Real.log (320 / 387) ∧
    -Real.log (320 / 387) ≤ (95051849 / 500000000) := by
  have h := checkLog_sound (w := (67 / 707)) (n := 12)
    (lo := (190103697 / 1000000000)) (hi := (95051849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387 / 320) = 1/(320 / 387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (190103697 / 1000000000) (95051849 / 500000000) (Real.log (387 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (387 / 320) = -Real.log (320 / 387) := by
    rw [show ((387 / 320) : ℝ) = ((320 / 387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (234931507 / 1000000000) ≤ -Real.log (253 / 320) ∧
    -Real.log (253 / 320) ≤ (58732877 / 250000000) := by
  have h := checkLog_sound (w := (67 / 573)) (n := 12)
    (lo := (234931507 / 1000000000)) (hi := (58732877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 253) = 1/(253 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58732877 / 250000000) (-234931507 / 1000000000) (Real.log (253 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (189861419 / 1000000000) ≤ -Real.log (10240 / 12381) ∧
    -Real.log (10240 / 12381) ≤ (9493071 / 50000000) := by
  have h := checkLog_sound (w := (2141 / 22621)) (n := 12)
    (lo := (189861419 / 1000000000)) (hi := (9493071 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12381 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12381 / 10240) = 1/(10240 / 12381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (189861419 / 1000000000) (9493071 / 50000000) (Real.log (12381 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12381 / 10240) = -Real.log (10240 / 12381) := by
    rw [show ((12381 / 10240) : ℝ) = ((10240 / 12381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (117280511 / 500000000) ≤ -Real.log (8099 / 10240) ∧
    -Real.log (8099 / 10240) ≤ (234561023 / 1000000000) := by
  have h := checkLog_sound (w := (2141 / 18339)) (n := 12)
    (lo := (117280511 / 500000000)) (hi := (234561023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8099) = 1/(8099 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-234561023 / 1000000000) (-117280511 / 500000000) (Real.log (8099 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (174888101 / 500000000) ≤ -Real.log (160 / 227) ∧
    -Real.log (160 / 227) ≤ (349776203 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 387)) (n := 12)
    (lo := (174888101 / 500000000)) (hi := (349776203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227 / 160) = 1/(160 / 227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (174888101 / 500000000) (349776203 / 1000000000) (Real.log (227 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (227 / 160) = -Real.log (160 / 227) := by
    rw [show ((227 / 160) : ℝ) = ((160 / 227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (271287161 / 500000000) ≤ -Real.log (93 / 160) ∧
    -Real.log (93 / 160) ≤ (542574323 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 93) = 1/(93 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-542574323 / 1000000000) (-271287161 / 500000000) (Real.log (93 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (349363121 / 1000000000) ≤ -Real.log (5120 / 7261) ∧
    -Real.log (5120 / 7261) ≤ (174681561 / 500000000) := by
  have h := checkLog_sound (w := (2141 / 12381)) (n := 12)
    (lo := (349363121 / 1000000000)) (hi := (174681561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7261 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7261 / 5120) = 1/(5120 / 7261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (349363121 / 1000000000) (174681561 / 500000000) (Real.log (7261 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7261 / 5120) = -Real.log (5120 / 7261) := by
    rw [show ((7261 / 5120) : ℝ) = ((5120 / 7261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (108313353 / 200000000) ≤ -Real.log (2979 / 5120) ∧
    -Real.log (2979 / 5120) ≤ (270783383 / 500000000) := by
  have h := checkLog_sound (w := (2141 / 8099)) (n := 12)
    (lo := (108313353 / 200000000)) (hi := (270783383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2979) = 1/(2979 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-270783383 / 500000000) (-108313353 / 200000000) (Real.log (2979 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (260834633 / 1000000000) ≤ -Real.log (1000000 / 1298013) ∧
    -Real.log (1000000 / 1298013) ≤ (130417317 / 500000000) := by
  have h := checkLog_sound (w := (298013 / 2298013)) (n := 12)
    (lo := (260834633 / 1000000000)) (hi := (130417317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1298013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1298013 / 1000000) = 1/(1000000 / 1298013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (260834633 / 1000000000) (130417317 / 500000000) (Real.log (1298013 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1298013 / 1000000) = -Real.log (1000000 / 1298013) := by
    rw [show ((1298013 / 1000000) : ℝ) = ((1000000 / 1298013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (353840393 / 1000000000) ≤ -Real.log (701987 / 1000000) ∧
    -Real.log (701987 / 1000000) ≤ (176920197 / 500000000) := by
  have h := checkLog_sound (w := (298013 / 1701987)) (n := 12)
    (lo := (353840393 / 1000000000)) (hi := (176920197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 701987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 701987) = 1/(701987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-176920197 / 500000000) (-353840393 / 1000000000) (Real.log (701987 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (261162773 / 1000000000) ≤ -Real.log (1000000 / 1298439) ∧
    -Real.log (1000000 / 1298439) ≤ (130581387 / 500000000) := by
  have h := checkLog_sound (w := (298439 / 2298439)) (n := 12)
    (lo := (261162773 / 1000000000)) (hi := (130581387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1298439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1298439 / 1000000) = 1/(1000000 / 1298439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (261162773 / 1000000000) (130581387 / 500000000) (Real.log (1298439 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1298439 / 1000000) = -Real.log (1000000 / 1298439) := by
    rw [show ((1298439 / 1000000) : ℝ) = ((1000000 / 1298439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (177223713 / 500000000) ≤ -Real.log (701561 / 1000000) ∧
    -Real.log (701561 / 1000000) ≤ (354447427 / 1000000000) := by
  have h := checkLog_sound (w := (298439 / 1701561)) (n := 12)
    (lo := (177223713 / 500000000)) (hi := (354447427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 701561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 701561) = 1/(701561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-354447427 / 1000000000) (-177223713 / 500000000) (Real.log (701561 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (39119771 / 200000000) ≤ -Real.log (1000000 / 1216039) ∧
    -Real.log (1000000 / 1216039) ≤ (24449857 / 125000000) := by
  have h := checkLog_sound (w := (216039 / 2216039)) (n := 12)
    (lo := (39119771 / 200000000)) (hi := (24449857 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1216039 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1216039 / 1000000) = 1/(1000000 / 1216039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (39119771 / 200000000) (24449857 / 125000000) (Real.log (1216039 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1216039 / 1000000) = -Real.log (1000000 / 1216039) := by
    rw [show ((1216039 / 1000000) : ℝ) = ((1000000 / 1216039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (60849001 / 250000000) ≤ -Real.log (783961 / 1000000) ∧
    -Real.log (783961 / 1000000) ≤ (48679201 / 200000000) := by
  have h := checkLog_sound (w := (216039 / 1783961)) (n := 12)
    (lo := (60849001 / 250000000)) (hi := (48679201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 783961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 783961) = 1/(783961 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-48679201 / 200000000) (-60849001 / 250000000) (Real.log (783961 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1224163 / 6250000) ≤ -Real.log (250000 / 304091) ∧
    -Real.log (250000 / 304091) ≤ (195866081 / 1000000000) := by
  have h := checkLog_sound (w := (54091 / 554091)) (n := 12)
    (lo := (1224163 / 6250000)) (hi := (195866081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304091 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304091 / 250000) = 1/(250000 / 304091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1224163 / 6250000) (195866081 / 1000000000) (Real.log (304091 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (304091 / 250000) = -Real.log (250000 / 304091) := by
    rw [show ((304091 / 250000) : ℝ) = ((250000 / 304091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (60952663 / 250000000) ≤ -Real.log (195909 / 250000) ∧
    -Real.log (195909 / 250000) ≤ (243810653 / 1000000000) := by
  have h := checkLog_sound (w := (54091 / 445909)) (n := 12)
    (lo := (60952663 / 250000000)) (hi := (243810653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 195909) = 1/(195909 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-243810653 / 1000000000) (-60952663 / 250000000) (Real.log (195909 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (614675027 / 1000000000) ≤ -Real.log (100000000000 / 184905560929) ∧
    -Real.log (100000000000 / 184905560929) ≤ (153668757 / 250000000) := by
  have h := checkLog_sound (w := (84905560929 / 284905560929)) (n := 12)
    (lo := (614675027 / 1000000000)) (hi := (153668757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184905560929 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184905560929 / 100000000000) = 1/(100000000000 / 184905560929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (614675027 / 1000000000) (153668757 / 250000000) (Real.log (184905560929 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (184905560929 / 100000000000) = -Real.log (100000000000 / 184905560929) := by
    rw [show ((184905560929 / 100000000000) : ℝ) = ((100000000000 / 184905560929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3078051 / 5000000) ≤ -Real.log (250000000000 / 462696401311) ∧
    -Real.log (250000000000 / 462696401311) ≤ (615610201 / 1000000000) := by
  have h := checkLog_sound (w := (212696401311 / 712696401311)) (n := 12)
    (lo := (3078051 / 5000000)) (hi := (615610201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462696401311 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(462696401311 / 250000000000) = 1/(250000000000 / 462696401311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3078051 / 5000000) (615610201 / 1000000000) (Real.log (462696401311 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (462696401311 / 250000000000) = -Real.log (250000000000 / 462696401311) := by
    rw [show ((462696401311 / 250000000000) : ℝ) = ((250000000000 / 462696401311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21949743 / 50000000) ≤ -Real.log (500000000000 / 775573657363) ∧
    -Real.log (500000000000 / 775573657363) ≤ (438994861 / 1000000000) := by
  have h := checkLog_sound (w := (275573657363 / 1275573657363)) (n := 12)
    (lo := (21949743 / 50000000)) (hi := (438994861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775573657363 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775573657363 / 500000000000) = 1/(500000000000 / 775573657363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (21949743 / 50000000) (438994861 / 1000000000) (Real.log (775573657363 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (775573657363 / 500000000000) = -Real.log (500000000000 / 775573657363) := by
    rw [show ((775573657363 / 500000000000) : ℝ) = ((500000000000 / 775573657363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (439676733 / 1000000000) ≤ -Real.log (500000000000 / 776102680327) ∧
    -Real.log (500000000000 / 776102680327) ≤ (219838367 / 500000000) := by
  have h := checkLog_sound (w := (276102680327 / 1276102680327)) (n := 12)
    (lo := (439676733 / 1000000000)) (hi := (219838367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776102680327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776102680327 / 500000000000) = 1/(500000000000 / 776102680327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (439676733 / 1000000000) (219838367 / 500000000) (Real.log (776102680327 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (776102680327 / 500000000000) = -Real.log (500000000000 / 776102680327) := by
    rw [show ((776102680327 / 500000000000) : ℝ) = ((500000000000 / 776102680327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0442

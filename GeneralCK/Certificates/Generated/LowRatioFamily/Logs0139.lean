import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8896_neg : (314026047 / 1000000000) ≤ -Real.log (1461 / 2000) ∧
    -Real.log (1461 / 2000) ≤ (4906657 / 15625000) := by
  have h := checkLog_sound (w := (539 / 3461)) (n := 12)
    (lo := (314026047 / 1000000000)) (hi := (4906657 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1461) = 1/(1461 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8896 : Bounds (-4906657 / 15625000) (-314026047 / 1000000000) (Real.log (1461 / 2000)) := by
  have h := reflection_log_8896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8897_neg : (269463 / 1000000000) ≤ -Real.log (2000000 / 2000539) ∧
    -Real.log (2000000 / 2000539) ≤ (33683 / 125000000) := by
  have h := checkLog_sound (w := (539 / 4000539)) (n := 12)
    (lo := (269463 / 1000000000)) (hi := (33683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000539 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000539 / 2000000) = 1/(2000000 / 2000539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8897 : Bounds (269463 / 1000000000) (33683 / 125000000) (Real.log (2000539 / 2000000)) := by
  have h := reflection_log_8897_neg
  have he : Real.log (2000539 / 2000000) = -Real.log (2000000 / 2000539) := by
    rw [show ((2000539 / 2000000) : ℝ) = ((2000000 / 2000539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8898_neg : (8423 / 31250000) ≤ -Real.log (1999461 / 2000000) ∧
    -Real.log (1999461 / 2000000) ≤ (269537 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 3999461)) (n := 12)
    (lo := (8423 / 31250000)) (hi := (269537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999461) = 1/(1999461 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8898 : Bounds (-269537 / 1000000000) (-8423 / 31250000) (Real.log (1999461 / 2000000)) := by
  have h := reflection_log_8898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8899_neg : (25530831 / 200000000) ≤ -Real.log (6250 / 7101) ∧
    -Real.log (6250 / 7101) ≤ (31913539 / 250000000) := by
  have h := checkLog_sound (w := (851 / 13351)) (n := 12)
    (lo := (25530831 / 200000000)) (hi := (31913539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7101 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7101 / 6250) = 1/(6250 / 7101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8899 : Bounds (25530831 / 200000000) (31913539 / 250000000) (Real.log (7101 / 6250)) := by
  have h := reflection_log_8899_neg
  have he : Real.log (7101 / 6250) = -Real.log (6250 / 7101) := by
    rw [show ((7101 / 6250) : ℝ) = ((6250 / 7101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8900_neg : (4573991 / 31250000) ≤ -Real.log (5399 / 6250) ∧
    -Real.log (5399 / 6250) ≤ (146367713 / 1000000000) := by
  have h := checkLog_sound (w := (851 / 11649)) (n := 12)
    (lo := (4573991 / 31250000)) (hi := (146367713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 5399) = 1/(5399 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8900 : Bounds (-146367713 / 1000000000) (-4573991 / 31250000) (Real.log (5399 / 6250)) := by
  have h := reflection_log_8900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8901_neg : (128117891 / 1000000000) ≤ -Real.log (1000000 / 1136687) ∧
    -Real.log (1000000 / 1136687) ≤ (32029473 / 250000000) := by
  have h := checkLog_sound (w := (136687 / 2136687)) (n := 12)
    (lo := (128117891 / 1000000000)) (hi := (32029473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136687 / 1000000) = 1/(1000000 / 1136687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8901 : Bounds (128117891 / 1000000000) (32029473 / 250000000) (Real.log (1136687 / 1000000)) := by
  have h := reflection_log_8901_neg
  have he : Real.log (1136687 / 1000000) = -Real.log (1000000 / 1136687) := by
    rw [show ((1136687 / 1000000) : ℝ) = ((1000000 / 1136687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8902_neg : (29395593 / 200000000) ≤ -Real.log (863313 / 1000000) ∧
    -Real.log (863313 / 1000000) ≤ (73488983 / 500000000) := by
  have h := checkLog_sound (w := (136687 / 1863313)) (n := 12)
    (lo := (29395593 / 200000000)) (hi := (73488983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863313) = 1/(863313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8902 : Bounds (-73488983 / 500000000) (-29395593 / 200000000) (Real.log (863313 / 1000000)) := by
  have h := reflection_log_8902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8903_neg : (9430037 / 500000000) ≤ -Real.log (981316664031 / 1000000000000) ∧
    -Real.log (981316664031 / 1000000000000) ≤ (754403 / 40000000) := by
  have h := checkLog_sound (w := (18683335969 / 1981316664031)) (n := 12)
    (lo := (9430037 / 500000000)) (hi := (754403 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981316664031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981316664031) = 1/(981316664031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8903 : Bounds (-754403 / 40000000) (-9430037 / 500000000) (Real.log (981316664031 / 1000000000000)) := by
  have h := reflection_log_8903_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8904_neg : (18713557 / 1000000000) ≤ -Real.log (38338299 / 39062500) ∧
    -Real.log (38338299 / 39062500) ≤ (9356779 / 500000000) := by
  have h := checkLog_sound (w := (724201 / 77400799)) (n := 12)
    (lo := (18713557 / 1000000000)) (hi := (9356779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 38338299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 38338299) = 1/(38338299 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8904 : Bounds (-9356779 / 500000000) (-18713557 / 1000000000) (Real.log (38338299 / 39062500)) := by
  have h := reflection_log_8904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8905_neg : (274021867 / 1000000000) ≤ -Real.log (500000000000 / 657621781811) ∧
    -Real.log (500000000000 / 657621781811) ≤ (68505467 / 250000000) := by
  have h := checkLog_sound (w := (157621781811 / 1157621781811)) (n := 12)
    (lo := (274021867 / 1000000000)) (hi := (68505467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657621781811 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657621781811 / 500000000000) = 1/(500000000000 / 657621781811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8905 : Bounds (274021867 / 1000000000) (68505467 / 250000000) (Real.log (657621781811 / 500000000000)) := by
  have h := reflection_log_8905_neg
  have he : Real.log (657621781811 / 500000000000) = -Real.log (500000000000 / 657621781811) := by
    rw [show ((657621781811 / 500000000000) : ℝ) = ((500000000000 / 657621781811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8906_neg : (17193491 / 62500000) ≤ -Real.log (125000000000 / 164582109849) ∧
    -Real.log (125000000000 / 164582109849) ≤ (275095857 / 1000000000) := by
  have h := checkLog_sound (w := (39582109849 / 289582109849)) (n := 12)
    (lo := (17193491 / 62500000)) (hi := (275095857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164582109849 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164582109849 / 125000000000) = 1/(125000000000 / 164582109849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8906 : Bounds (17193491 / 62500000) (275095857 / 1000000000) (Real.log (164582109849 / 125000000000)) := by
  have h := reflection_log_8906_neg
  have he : Real.log (164582109849 / 125000000000) = -Real.log (125000000000 / 164582109849) := by
    rw [show ((164582109849 / 125000000000) : ℝ) = ((125000000000 / 164582109849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8907_neg : (551571007 / 1000000000) ≤ -Real.log (500000000000 / 867989056087) ∧
    -Real.log (500000000000 / 867989056087) ≤ (8618297 / 15625000) := by
  have h := checkLog_sound (w := (367989056087 / 1367989056087)) (n := 12)
    (lo := (551571007 / 1000000000)) (hi := (8618297 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867989056087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(867989056087 / 500000000000) = 1/(500000000000 / 867989056087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8907 : Bounds (551571007 / 1000000000) (8618297 / 15625000) (Real.log (867989056087 / 500000000000)) := by
  have h := reflection_log_8907_neg
  have he : Real.log (867989056087 / 500000000000) = -Real.log (500000000000 / 867989056087) := by
    rw [show ((867989056087 / 500000000000) : ℝ) = ((500000000000 / 867989056087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8908_neg : (552649169 / 1000000000) ≤ -Real.log (500000000000 / 868925393567) ∧
    -Real.log (500000000000 / 868925393567) ≤ (55264917 / 100000000) := by
  have h := checkLog_sound (w := (368925393567 / 1368925393567)) (n := 12)
    (lo := (552649169 / 1000000000)) (hi := (55264917 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((868925393567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(868925393567 / 500000000000) = 1/(500000000000 / 868925393567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8908 : Bounds (552649169 / 1000000000) (55264917 / 100000000) (Real.log (868925393567 / 500000000000)) := by
  have h := reflection_log_8908_neg
  have he : Real.log (868925393567 / 500000000000) = -Real.log (500000000000 / 868925393567) := by
    rw [show ((868925393567 / 500000000000) : ℝ) = ((500000000000 / 868925393567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8909_neg : (2390169 / 10000000) ≤ -Real.log (100 / 127) ∧
    -Real.log (100 / 127) ≤ (239016901 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 227)) (n := 12)
    (lo := (2390169 / 10000000)) (hi := (239016901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127 / 100) = 1/(100 / 127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8909 : Bounds (2390169 / 10000000) (239016901 / 1000000000) (Real.log (127 / 100)) := by
  have h := reflection_log_8909_neg
  have he : Real.log (127 / 100) = -Real.log (100 / 127) := by
    rw [show ((127 / 100) : ℝ) = ((100 / 127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8910_neg : (39338843 / 125000000) ≤ -Real.log (73 / 100) ∧
    -Real.log (73 / 100) ≤ (62942149 / 200000000) := by
  have h := checkLog_sound (w := (27 / 173)) (n := 12)
    (lo := (39338843 / 125000000)) (hi := (62942149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 73) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 73) = 1/(73 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8910 : Bounds (-62942149 / 200000000) (-39338843 / 125000000) (Real.log (73 / 100)) := by
  have h := reflection_log_8910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8911_neg : (269963 / 1000000000) ≤ -Real.log (100000 / 100027) ∧
    -Real.log (100000 / 100027) ≤ (67491 / 250000000) := by
  have h := checkLog_sound (w := (27 / 200027)) (n := 12)
    (lo := (269963 / 1000000000)) (hi := (67491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100027 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100027 / 100000) = 1/(100000 / 100027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8911 : Bounds (269963 / 1000000000) (67491 / 250000000) (Real.log (100027 / 100000)) := by
  have h := reflection_log_8911_neg
  have he : Real.log (100027 / 100000) = -Real.log (100000 / 100027) := by
    rw [show ((100027 / 100000) : ℝ) = ((100000 / 100027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8912_neg : (67509 / 250000000) ≤ -Real.log (99973 / 100000) ∧
    -Real.log (99973 / 100000) ≤ (270037 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 199973)) (n := 12)
    (lo := (67509 / 250000000)) (hi := (270037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99973) = 1/(99973 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8912 : Bounds (-270037 / 1000000000) (-67509 / 250000000) (Real.log (99973 / 100000)) := by
  have h := reflection_log_8912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8913_neg : (12788297 / 100000000) ≤ -Real.log (50000 / 56821) ∧
    -Real.log (50000 / 56821) ≤ (127882971 / 1000000000) := by
  have h := checkLog_sound (w := (6821 / 106821)) (n := 12)
    (lo := (12788297 / 100000000)) (hi := (127882971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56821 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56821 / 50000) = 1/(50000 / 56821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8913 : Bounds (12788297 / 100000000) (127882971 / 1000000000) (Real.log (56821 / 50000)) := by
  have h := reflection_log_8913_neg
  have he : Real.log (56821 / 50000) = -Real.log (50000 / 56821) := by
    rw [show ((56821 / 50000) : ℝ) = ((50000 / 56821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8914_neg : (146668739 / 1000000000) ≤ -Real.log (43179 / 50000) ∧
    -Real.log (43179 / 50000) ≤ (7333437 / 50000000) := by
  have h := checkLog_sound (w := (6821 / 93179)) (n := 12)
    (lo := (146668739 / 1000000000)) (hi := (7333437 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43179) = 1/(43179 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8914 : Bounds (-7333437 / 50000000) (-146668739 / 1000000000) (Real.log (43179 / 50000)) := by
  have h := reflection_log_8914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8915_neg : (128346599 / 1000000000) ≤ -Real.log (1000000 / 1136947) ∧
    -Real.log (1000000 / 1136947) ≤ (641733 / 5000000) := by
  have h := checkLog_sound (w := (136947 / 2136947)) (n := 12)
    (lo := (128346599 / 1000000000)) (hi := (641733 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136947 / 1000000) = 1/(1000000 / 1136947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8915 : Bounds (128346599 / 1000000000) (641733 / 5000000) (Real.log (1136947 / 1000000)) := by
  have h := reflection_log_8915_neg
  have he : Real.log (1136947 / 1000000) = -Real.log (1000000 / 1136947) := by
    rw [show ((1136947 / 1000000) : ℝ) = ((1000000 / 1136947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8916_neg : (18409897 / 125000000) ≤ -Real.log (863053 / 1000000) ∧
    -Real.log (863053 / 1000000) ≤ (147279177 / 1000000000) := by
  have h := checkLog_sound (w := (136947 / 1863053)) (n := 12)
    (lo := (18409897 / 125000000)) (hi := (147279177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863053) = 1/(863053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8916 : Bounds (-147279177 / 1000000000) (-18409897 / 125000000) (Real.log (863053 / 1000000)) := by
  have h := reflection_log_8916_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8917_neg : (591643 / 31250000) ≤ -Real.log (981245519191 / 1000000000000) ∧
    -Real.log (981245519191 / 1000000000000) ≤ (18932577 / 1000000000) := by
  have h := checkLog_sound (w := (18754480809 / 1981245519191)) (n := 12)
    (lo := (591643 / 31250000)) (hi := (18932577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981245519191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981245519191) = 1/(981245519191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8917 : Bounds (-18932577 / 1000000000) (-591643 / 31250000) (Real.log (981245519191 / 1000000000000)) := by
  have h := reflection_log_8917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8918_neg : (18785769 / 1000000000) ≤ -Real.log (2453473959 / 2500000000) ∧
    -Real.log (2453473959 / 2500000000) ≤ (1878577 / 100000000) := by
  have h := checkLog_sound (w := (46526041 / 4953473959)) (n := 12)
    (lo := (18785769 / 1000000000)) (hi := (1878577 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2453473959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2453473959) = 1/(2453473959 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8918 : Bounds (-1878577 / 100000000) (-18785769 / 1000000000) (Real.log (2453473959 / 2500000000)) := by
  have h := reflection_log_8918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8919_neg : (274551709 / 1000000000) ≤ -Real.log (500000000000 / 657970309641) ∧
    -Real.log (500000000000 / 657970309641) ≤ (27455171 / 100000000) := by
  have h := checkLog_sound (w := (157970309641 / 1157970309641)) (n := 12)
    (lo := (274551709 / 1000000000)) (hi := (27455171 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657970309641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657970309641 / 500000000000) = 1/(500000000000 / 657970309641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8919 : Bounds (274551709 / 1000000000) (27455171 / 100000000) (Real.log (657970309641 / 500000000000)) := by
  have h := reflection_log_8919_neg
  have he : Real.log (657970309641 / 500000000000) = -Real.log (500000000000 / 657970309641) := by
    rw [show ((657970309641 / 500000000000) : ℝ) = ((500000000000 / 657970309641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8920_neg : (11025031 / 40000000) ≤ -Real.log (50000000000 / 65867739293) ∧
    -Real.log (50000000000 / 65867739293) ≤ (17226611 / 62500000) := by
  have h := checkLog_sound (w := (15867739293 / 115867739293)) (n := 12)
    (lo := (11025031 / 40000000)) (hi := (17226611 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65867739293 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65867739293 / 50000000000) = 1/(50000000000 / 65867739293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8920 : Bounds (11025031 / 40000000) (17226611 / 62500000) (Real.log (65867739293 / 50000000000)) := by
  have h := reflection_log_8920_neg
  have he : Real.log (65867739293 / 50000000000) = -Real.log (50000000000 / 65867739293) := by
    rw [show ((65867739293 / 50000000000) : ℝ) = ((50000000000 / 65867739293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8921_neg : (552649169 / 1000000000) ≤ -Real.log (250000000000 / 434462696783) ∧
    -Real.log (250000000000 / 434462696783) ≤ (55264917 / 100000000) := by
  have h := checkLog_sound (w := (184462696783 / 684462696783)) (n := 12)
    (lo := (552649169 / 1000000000)) (hi := (55264917 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((434462696783 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(434462696783 / 250000000000) = 1/(250000000000 / 434462696783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8921 : Bounds (552649169 / 1000000000) (55264917 / 100000000) (Real.log (434462696783 / 250000000000)) := by
  have h := reflection_log_8921_neg
  have he : Real.log (434462696783 / 250000000000) = -Real.log (250000000000 / 434462696783) := by
    rw [show ((434462696783 / 250000000000) : ℝ) = ((250000000000 / 434462696783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8922_neg : (110745529 / 200000000) ≤ -Real.log (500000000000 / 869863013699) ∧
    -Real.log (500000000000 / 869863013699) ≤ (276863823 / 500000000) := by
  have h := checkLog_sound (w := (369863013699 / 1369863013699)) (n := 12)
    (lo := (110745529 / 200000000)) (hi := (276863823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869863013699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869863013699 / 500000000000) = 1/(500000000000 / 869863013699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8922 : Bounds (110745529 / 200000000) (276863823 / 500000000) (Real.log (869863013699 / 500000000000)) := by
  have h := reflection_log_8922_neg
  have he : Real.log (869863013699 / 500000000000) = -Real.log (500000000000 / 869863013699) := by
    rw [show ((869863013699 / 500000000000) : ℝ) = ((500000000000 / 869863013699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8923_neg : (239410523 / 1000000000) ≤ -Real.log (2000 / 2541) ∧
    -Real.log (2000 / 2541) ≤ (59852631 / 250000000) := by
  have h := checkLog_sound (w := (541 / 4541)) (n := 12)
    (lo := (239410523 / 1000000000)) (hi := (59852631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2541 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2541 / 2000) = 1/(2000 / 2541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8923 : Bounds (239410523 / 1000000000) (59852631 / 250000000) (Real.log (2541 / 2000)) := by
  have h := reflection_log_8923_neg
  have he : Real.log (2541 / 2000) = -Real.log (2000 / 2541) := by
    rw [show ((2541 / 2000) : ℝ) = ((2000 / 2541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8924_neg : (315395911 / 1000000000) ≤ -Real.log (1459 / 2000) ∧
    -Real.log (1459 / 2000) ≤ (39424489 / 125000000) := by
  have h := checkLog_sound (w := (541 / 3459)) (n := 12)
    (lo := (315395911 / 1000000000)) (hi := (39424489 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1459) = 1/(1459 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8924 : Bounds (-39424489 / 125000000) (-315395911 / 1000000000) (Real.log (1459 / 2000)) := by
  have h := reflection_log_8924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8925_neg : (270463 / 1000000000) ≤ -Real.log (2000000 / 2000541) ∧
    -Real.log (2000000 / 2000541) ≤ (2113 / 7812500) := by
  have h := checkLog_sound (w := (541 / 4000541)) (n := 12)
    (lo := (270463 / 1000000000)) (hi := (2113 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000541 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000541 / 2000000) = 1/(2000000 / 2000541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8925 : Bounds (270463 / 1000000000) (2113 / 7812500) (Real.log (2000541 / 2000000)) := by
  have h := reflection_log_8925_neg
  have he : Real.log (2000541 / 2000000) = -Real.log (2000000 / 2000541) := by
    rw [show ((2000541 / 2000000) : ℝ) = ((2000000 / 2000541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8926_neg : (33817 / 125000000) ≤ -Real.log (1999459 / 2000000) ∧
    -Real.log (1999459 / 2000000) ≤ (270537 / 1000000000) := by
  have h := checkLog_sound (w := (541 / 3999459)) (n := 12)
    (lo := (33817 / 125000000)) (hi := (270537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999459) = 1/(1999459 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8926 : Bounds (-270537 / 1000000000) (-33817 / 125000000) (Real.log (1999459 / 2000000)) := by
  have h := reflection_log_8926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8927_neg : (32027933 / 250000000) ≤ -Real.log (25000 / 28417) ∧
    -Real.log (25000 / 28417) ≤ (128111733 / 1000000000) := by
  have h := checkLog_sound (w := (3417 / 53417)) (n := 12)
    (lo := (32027933 / 250000000)) (hi := (128111733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28417 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28417 / 25000) = 1/(25000 / 28417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8927 : Bounds (32027933 / 250000000) (128111733 / 1000000000) (Real.log (28417 / 25000)) := by
  have h := reflection_log_8927_neg
  have he : Real.log (28417 / 25000) = -Real.log (25000 / 28417) := by
    rw [show ((28417 / 25000) : ℝ) = ((25000 / 28417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8928_neg : (146969857 / 1000000000) ≤ -Real.log (21583 / 25000) ∧
    -Real.log (21583 / 25000) ≤ (73484929 / 500000000) := by
  have h := checkLog_sound (w := (3417 / 46583)) (n := 12)
    (lo := (146969857 / 1000000000)) (hi := (73484929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21583) = 1/(21583 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8928 : Bounds (-73484929 / 500000000) (-146969857 / 1000000000) (Real.log (21583 / 25000)) := by
  have h := reflection_log_8928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8929_neg : (25715227 / 200000000) ≤ -Real.log (125000 / 142151) ∧
    -Real.log (125000 / 142151) ≤ (16072017 / 125000000) := by
  have h := checkLog_sound (w := (17151 / 267151)) (n := 12)
    (lo := (25715227 / 200000000)) (hi := (16072017 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142151 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142151 / 125000) = 1/(125000 / 142151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8929 : Bounds (25715227 / 200000000) (16072017 / 125000000) (Real.log (142151 / 125000)) := by
  have h := reflection_log_8929_neg
  have he : Real.log (142151 / 125000) = -Real.log (125000 / 142151) := by
    rw [show ((142151 / 125000) : ℝ) = ((125000 / 142151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8930_neg : (36895409 / 250000000) ≤ -Real.log (107849 / 125000) ∧
    -Real.log (107849 / 125000) ≤ (147581637 / 1000000000) := by
  have h := checkLog_sound (w := (17151 / 232849)) (n := 12)
    (lo := (36895409 / 250000000)) (hi := (147581637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107849) = 1/(107849 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8930 : Bounds (-147581637 / 1000000000) (-36895409 / 250000000) (Real.log (107849 / 125000)) := by
  have h := reflection_log_8930_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8931_neg : (19005501 / 1000000000) ≤ -Real.log (15330843199 / 15625000000) ∧
    -Real.log (15330843199 / 15625000000) ≤ (9502751 / 500000000) := by
  have h := checkLog_sound (w := (294156801 / 30955843199)) (n := 12)
    (lo := (19005501 / 1000000000)) (hi := (9502751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15330843199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15330843199) = 1/(15330843199 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8931 : Bounds (-9502751 / 500000000) (-19005501 / 1000000000) (Real.log (15330843199 / 15625000000)) := by
  have h := reflection_log_8931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8932_neg : (4714531 / 250000000) ≤ -Real.log (613324111 / 625000000) ∧
    -Real.log (613324111 / 625000000) ≤ (30173 / 1600000) := by
  have h := checkLog_sound (w := (11675889 / 1238324111)) (n := 12)
    (lo := (4714531 / 250000000)) (hi := (30173 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 613324111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 613324111) = 1/(613324111 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8932 : Bounds (-30173 / 1600000) (-4714531 / 250000000) (Real.log (613324111 / 625000000)) := by
  have h := reflection_log_8932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8933_neg : (275081589 / 1000000000) ≤ -Real.log (250000000000 / 329159523699) ∧
    -Real.log (250000000000 / 329159523699) ≤ (27508159 / 100000000) := by
  have h := checkLog_sound (w := (79159523699 / 579159523699)) (n := 12)
    (lo := (275081589 / 1000000000)) (hi := (27508159 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329159523699 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329159523699 / 250000000000) = 1/(250000000000 / 329159523699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8933 : Bounds (275081589 / 1000000000) (27508159 / 100000000) (Real.log (329159523699 / 250000000000)) := by
  have h := reflection_log_8933_neg
  have he : Real.log (329159523699 / 250000000000) = -Real.log (250000000000 / 329159523699) := by
    rw [show ((329159523699 / 250000000000) : ℝ) = ((250000000000 / 329159523699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8934_neg : (69039443 / 250000000) ≤ -Real.log (12500000000 / 16475697503) ∧
    -Real.log (12500000000 / 16475697503) ≤ (276157773 / 1000000000) := by
  have h := checkLog_sound (w := (3975697503 / 28975697503)) (n := 12)
    (lo := (69039443 / 250000000)) (hi := (276157773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16475697503 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16475697503 / 12500000000) = 1/(12500000000 / 16475697503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8934 : Bounds (69039443 / 250000000) (276157773 / 1000000000) (Real.log (16475697503 / 12500000000)) := by
  have h := reflection_log_8934_neg
  have he : Real.log (16475697503 / 12500000000) = -Real.log (12500000000 / 16475697503) := by
    rw [show ((16475697503 / 12500000000) : ℝ) = ((12500000000 / 16475697503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8935_neg : (110745529 / 200000000) ≤ -Real.log (250000000000 / 434931506849) ∧
    -Real.log (250000000000 / 434931506849) ≤ (276863823 / 500000000) := by
  have h := checkLog_sound (w := (184931506849 / 684931506849)) (n := 12)
    (lo := (110745529 / 200000000)) (hi := (276863823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((434931506849 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(434931506849 / 250000000000) = 1/(250000000000 / 434931506849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8935 : Bounds (110745529 / 200000000) (276863823 / 500000000) (Real.log (434931506849 / 250000000000)) := by
  have h := reflection_log_8935_neg
  have he : Real.log (434931506849 / 250000000000) = -Real.log (250000000000 / 434931506849) := by
    rw [show ((434931506849 / 250000000000) : ℝ) = ((250000000000 / 434931506849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8936_neg : (277403217 / 500000000) ≤ -Real.log (500000000000 / 870801919123) ∧
    -Real.log (500000000000 / 870801919123) ≤ (110961287 / 200000000) := by
  have h := checkLog_sound (w := (370801919123 / 1370801919123)) (n := 12)
    (lo := (277403217 / 500000000)) (hi := (110961287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((870801919123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(870801919123 / 500000000000) = 1/(500000000000 / 870801919123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8936 : Bounds (277403217 / 500000000) (110961287 / 200000000) (Real.log (870801919123 / 500000000000)) := by
  have h := reflection_log_8936_neg
  have he : Real.log (870801919123 / 500000000000) = -Real.log (500000000000 / 870801919123) := by
    rw [show ((870801919123 / 500000000000) : ℝ) = ((500000000000 / 870801919123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8937_neg : (29975499 / 125000000) ≤ -Real.log (1000 / 1271) ∧
    -Real.log (1000 / 1271) ≤ (239803993 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2271)) (n := 12)
    (lo := (29975499 / 125000000)) (hi := (239803993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271 / 1000) = 1/(1000 / 1271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8937 : Bounds (29975499 / 125000000) (239803993 / 1000000000) (Real.log (1271 / 1000)) := by
  have h := reflection_log_8937_neg
  have he : Real.log (1271 / 1000) = -Real.log (1000 / 1271) := by
    rw [show ((1271 / 1000) : ℝ) = ((1000 / 1271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8938_neg : (158040773 / 500000000) ≤ -Real.log (729 / 1000) ∧
    -Real.log (729 / 1000) ≤ (316081547 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1729)) (n := 12)
    (lo := (158040773 / 500000000)) (hi := (316081547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 729) = 1/(729 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8938 : Bounds (-316081547 / 1000000000) (-158040773 / 500000000) (Real.log (729 / 1000)) := by
  have h := reflection_log_8938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8939_neg : (270963 / 1000000000) ≤ -Real.log (1000000 / 1000271) ∧
    -Real.log (1000000 / 1000271) ≤ (67741 / 250000000) := by
  have h := checkLog_sound (w := (271 / 2000271)) (n := 12)
    (lo := (270963 / 1000000000)) (hi := (67741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000271 / 1000000) = 1/(1000000 / 1000271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8939 : Bounds (270963 / 1000000000) (67741 / 250000000) (Real.log (1000271 / 1000000)) := by
  have h := reflection_log_8939_neg
  have he : Real.log (1000271 / 1000000) = -Real.log (1000000 / 1000271) := by
    rw [show ((1000271 / 1000000) : ℝ) = ((1000000 / 1000271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8940_neg : (67759 / 250000000) ≤ -Real.log (999729 / 1000000) ∧
    -Real.log (999729 / 1000000) ≤ (271037 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1999729)) (n := 12)
    (lo := (67759 / 250000000)) (hi := (271037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999729) = 1/(999729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8940 : Bounds (-271037 / 1000000000) (-67759 / 250000000) (Real.log (999729 / 1000000)) := by
  have h := reflection_log_8940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8941_neg : (64170221 / 500000000) ≤ -Real.log (50000 / 56847) ∧
    -Real.log (50000 / 56847) ≤ (128340443 / 1000000000) := by
  have h := checkLog_sound (w := (6847 / 106847)) (n := 12)
    (lo := (64170221 / 500000000)) (hi := (128340443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56847 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56847 / 50000) = 1/(50000 / 56847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8941 : Bounds (64170221 / 500000000) (128340443 / 1000000000) (Real.log (56847 / 50000)) := by
  have h := reflection_log_8941_neg
  have he : Real.log (56847 / 50000) = -Real.log (50000 / 56847) := by
    rw [show ((56847 / 50000) : ℝ) = ((50000 / 56847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8942_neg : (29454213 / 200000000) ≤ -Real.log (43153 / 50000) ∧
    -Real.log (43153 / 50000) ≤ (73635533 / 500000000) := by
  have h := checkLog_sound (w := (6847 / 93153)) (n := 12)
    (lo := (29454213 / 200000000)) (hi := (73635533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43153) = 1/(43153 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8942 : Bounds (-73635533 / 500000000) (-29454213 / 200000000) (Real.log (43153 / 50000)) := by
  have h := reflection_log_8942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8943_neg : (128804739 / 1000000000) ≤ -Real.log (250000 / 284367) ∧
    -Real.log (250000 / 284367) ≤ (6440237 / 50000000) := by
  have h := checkLog_sound (w := (34367 / 534367)) (n := 12)
    (lo := (128804739 / 1000000000)) (hi := (6440237 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284367 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284367 / 250000) = 1/(250000 / 284367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8943 : Bounds (128804739 / 1000000000) (6440237 / 50000000) (Real.log (284367 / 250000)) := by
  have h := reflection_log_8943_neg
  have he : Real.log (284367 / 250000) = -Real.log (250000 / 284367) := by
    rw [show ((284367 / 250000) : ℝ) = ((250000 / 284367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8944_neg : (147883029 / 1000000000) ≤ -Real.log (215633 / 250000) ∧
    -Real.log (215633 / 250000) ≤ (14788303 / 100000000) := by
  have h := checkLog_sound (w := (34367 / 465633)) (n := 12)
    (lo := (147883029 / 1000000000)) (hi := (14788303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 215633) = 1/(215633 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8944 : Bounds (-14788303 / 100000000) (-147883029 / 1000000000) (Real.log (215633 / 250000)) := by
  have h := reflection_log_8944_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8945_neg : (19078289 / 1000000000) ≤ -Real.log (61318909311 / 62500000000) ∧
    -Real.log (61318909311 / 62500000000) ≤ (1907829 / 100000000) := by
  have h := checkLog_sound (w := (1181090689 / 123818909311)) (n := 12)
    (lo := (19078289 / 1000000000)) (hi := (1907829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61318909311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61318909311) = 1/(61318909311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8945 : Bounds (-1907829 / 100000000) (-19078289 / 1000000000) (Real.log (61318909311 / 62500000000)) := by
  have h := reflection_log_8945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8946_neg : (9465311 / 500000000) ≤ -Real.log (2453118591 / 2500000000) ∧
    -Real.log (2453118591 / 2500000000) ≤ (18930623 / 1000000000) := by
  have h := checkLog_sound (w := (46881409 / 4953118591)) (n := 12)
    (lo := (9465311 / 500000000)) (hi := (18930623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2453118591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2453118591) = 1/(2453118591 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8946 : Bounds (-18930623 / 1000000000) (-9465311 / 500000000) (Real.log (2453118591 / 2500000000)) := by
  have h := reflection_log_8946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8947_neg : (68902877 / 250000000) ≤ -Real.log (62500000000 / 82333499409) ∧
    -Real.log (62500000000 / 82333499409) ≤ (275611509 / 1000000000) := by
  have h := checkLog_sound (w := (19833499409 / 144833499409)) (n := 12)
    (lo := (68902877 / 250000000)) (hi := (275611509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82333499409 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82333499409 / 62500000000) = 1/(62500000000 / 82333499409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8947 : Bounds (68902877 / 250000000) (275611509 / 1000000000) (Real.log (82333499409 / 62500000000)) := by
  have h := reflection_log_8947_neg
  have he : Real.log (82333499409 / 62500000000) = -Real.log (62500000000 / 82333499409) := by
    rw [show ((82333499409 / 62500000000) : ℝ) = ((62500000000 / 82333499409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8948_neg : (34585971 / 125000000) ≤ -Real.log (250000000000 / 329688637639) ∧
    -Real.log (250000000000 / 329688637639) ≤ (276687769 / 1000000000) := by
  have h := checkLog_sound (w := (79688637639 / 579688637639)) (n := 12)
    (lo := (34585971 / 125000000)) (hi := (276687769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329688637639 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329688637639 / 250000000000) = 1/(250000000000 / 329688637639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8948 : Bounds (34585971 / 125000000) (276687769 / 1000000000) (Real.log (329688637639 / 250000000000)) := by
  have h := reflection_log_8948_neg
  have he : Real.log (329688637639 / 250000000000) = -Real.log (250000000000 / 329688637639) := by
    rw [show ((329688637639 / 250000000000) : ℝ) = ((250000000000 / 329688637639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8949_neg : (277403217 / 500000000) ≤ -Real.log (250000000000 / 435400959561) ∧
    -Real.log (250000000000 / 435400959561) ≤ (110961287 / 200000000) := by
  have h := checkLog_sound (w := (185400959561 / 685400959561)) (n := 12)
    (lo := (277403217 / 500000000)) (hi := (110961287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((435400959561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(435400959561 / 250000000000) = 1/(250000000000 / 435400959561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8949 : Bounds (277403217 / 500000000) (110961287 / 200000000) (Real.log (435400959561 / 250000000000)) := by
  have h := reflection_log_8949_neg
  have he : Real.log (435400959561 / 250000000000) = -Real.log (250000000000 / 435400959561) := by
    rw [show ((435400959561 / 250000000000) : ℝ) = ((250000000000 / 435400959561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8950_neg : (555885539 / 1000000000) ≤ -Real.log (500000000000 / 871742112483) ∧
    -Real.log (500000000000 / 871742112483) ≤ (27794277 / 50000000) := by
  have h := checkLog_sound (w := (371742112483 / 1371742112483)) (n := 12)
    (lo := (555885539 / 1000000000)) (hi := (27794277 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871742112483 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871742112483 / 500000000000) = 1/(500000000000 / 871742112483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8950 : Bounds (555885539 / 1000000000) (27794277 / 50000000) (Real.log (871742112483 / 500000000000)) := by
  have h := reflection_log_8950_neg
  have he : Real.log (871742112483 / 500000000000) = -Real.log (500000000000 / 871742112483) := by
    rw [show ((871742112483 / 500000000000) : ℝ) = ((500000000000 / 871742112483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8951_neg : (48039461 / 200000000) ≤ -Real.log (2000 / 2543) ∧
    -Real.log (2000 / 2543) ≤ (120098653 / 500000000) := by
  have h := checkLog_sound (w := (543 / 4543)) (n := 12)
    (lo := (48039461 / 200000000)) (hi := (120098653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2543 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2543 / 2000) = 1/(2000 / 2543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8951 : Bounds (48039461 / 200000000) (120098653 / 500000000) (Real.log (2543 / 2000)) := by
  have h := reflection_log_8951_neg
  have he : Real.log (2543 / 2000) = -Real.log (2000 / 2543) := by
    rw [show ((2543 / 2000) : ℝ) = ((2000 / 2543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8952_neg : (316767653 / 1000000000) ≤ -Real.log (1457 / 2000) ∧
    -Real.log (1457 / 2000) ≤ (158383827 / 500000000) := by
  have h := checkLog_sound (w := (543 / 3457)) (n := 12)
    (lo := (316767653 / 1000000000)) (hi := (158383827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1457) = 1/(1457 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8952 : Bounds (-158383827 / 500000000) (-316767653 / 1000000000) (Real.log (1457 / 2000)) := by
  have h := reflection_log_8952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8953_neg : (271463 / 1000000000) ≤ -Real.log (2000000 / 2000543) ∧
    -Real.log (2000000 / 2000543) ≤ (33933 / 125000000) := by
  have h := checkLog_sound (w := (543 / 4000543)) (n := 12)
    (lo := (271463 / 1000000000)) (hi := (33933 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000543 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000543 / 2000000) = 1/(2000000 / 2000543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8953 : Bounds (271463 / 1000000000) (33933 / 125000000) (Real.log (2000543 / 2000000)) := by
  have h := reflection_log_8953_neg
  have he : Real.log (2000543 / 2000000) = -Real.log (2000000 / 2000543) := by
    rw [show ((2000543 / 2000000) : ℝ) = ((2000000 / 2000543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8954_neg : (16971 / 62500000) ≤ -Real.log (1999457 / 2000000) ∧
    -Real.log (1999457 / 2000000) ≤ (271537 / 1000000000) := by
  have h := checkLog_sound (w := (543 / 3999457)) (n := 12)
    (lo := (16971 / 62500000)) (hi := (271537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999457) = 1/(1999457 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8954 : Bounds (-271537 / 1000000000) (-16971 / 62500000) (Real.log (1999457 / 2000000)) := by
  have h := reflection_log_8954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8955_neg : (1285691 / 10000000) ≤ -Real.log (2500 / 2843) ∧
    -Real.log (2500 / 2843) ≤ (128569101 / 1000000000) := by
  have h := checkLog_sound (w := (343 / 5343)) (n := 12)
    (lo := (1285691 / 10000000)) (hi := (128569101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2843 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2843 / 2500) = 1/(2500 / 2843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8955 : Bounds (1285691 / 10000000) (128569101 / 1000000000) (Real.log (2843 / 2500)) := by
  have h := reflection_log_8955_neg
  have he : Real.log (2843 / 2500) = -Real.log (2500 / 2843) := by
    rw [show ((2843 / 2500) : ℝ) = ((2500 / 2843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8956_neg : (36893091 / 250000000) ≤ -Real.log (2157 / 2500) ∧
    -Real.log (2157 / 2500) ≤ (29514473 / 200000000) := by
  have h := checkLog_sound (w := (343 / 4657)) (n := 12)
    (lo := (36893091 / 250000000)) (hi := (29514473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2157) = 1/(2157 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8956 : Bounds (-29514473 / 200000000) (-36893091 / 250000000) (Real.log (2157 / 2500)) := by
  have h := reflection_log_8956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8957_neg : (12903417 / 100000000) ≤ -Real.log (1000000 / 1137729) ∧
    -Real.log (1000000 / 1137729) ≤ (129034171 / 1000000000) := by
  have h := checkLog_sound (w := (137729 / 2137729)) (n := 12)
    (lo := (12903417 / 100000000)) (hi := (129034171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137729 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137729 / 1000000) = 1/(1000000 / 1137729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8957 : Bounds (12903417 / 100000000) (129034171 / 1000000000) (Real.log (1137729 / 1000000)) := by
  have h := reflection_log_8957_neg
  have he : Real.log (1137729 / 1000000) = -Real.log (1000000 / 1137729) := by
    rw [show ((1137729 / 1000000) : ℝ) = ((1000000 / 1137729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8958_neg : (18523209 / 125000000) ≤ -Real.log (862271 / 1000000) ∧
    -Real.log (862271 / 1000000) ≤ (148185673 / 1000000000) := by
  have h := checkLog_sound (w := (137729 / 1862271)) (n := 12)
    (lo := (18523209 / 125000000)) (hi := (148185673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862271) = 1/(862271 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8958 : Bounds (-148185673 / 1000000000) (-18523209 / 125000000) (Real.log (862271 / 1000000)) := by
  have h := reflection_log_8958_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8959_neg : (9575751 / 500000000) ≤ -Real.log (981030722559 / 1000000000000) ∧
    -Real.log (981030722559 / 1000000000000) ≤ (19151503 / 1000000000) := by
  have h := checkLog_sound (w := (18969277441 / 1981030722559)) (n := 12)
    (lo := (9575751 / 500000000)) (hi := (19151503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981030722559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981030722559) = 1/(981030722559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8959 : Bounds (-19151503 / 1000000000) (-9575751 / 500000000) (Real.log (981030722559 / 1000000000000)) := by
  have h := reflection_log_8959_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

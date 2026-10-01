import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0241
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

theorem reflection_log_1_neg : (123536839 / 500000000) ≤ -Real.log (1024 / 1311) ∧
    -Real.log (1024 / 1311) ≤ (247073679 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 2335)) (n := 12)
    (lo := (123536839 / 500000000)) (hi := (247073679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311 / 1024) = 1/(1024 / 1311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (123536839 / 500000000) (247073679 / 1000000000) (Real.log (1311 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1311 / 1024) = -Real.log (1024 / 1311) := by
    rw [show ((1311 / 1024) : ℝ) = ((1024 / 1311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (328883913 / 1000000000) ≤ -Real.log (737 / 1024) ∧
    -Real.log (737 / 1024) ≤ (164441957 / 500000000) := by
  have h := checkLog_sound (w := (287 / 1761)) (n := 12)
    (lo := (328883913 / 1000000000)) (hi := (164441957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 737) = 1/(737 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-164441957 / 500000000) (-328883913 / 1000000000) (Real.log (737 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (246615907 / 1000000000) ≤ -Real.log (640 / 819) ∧
    -Real.log (640 / 819) ≤ (61653977 / 250000000) := by
  have h := checkLog_sound (w := (179 / 1459)) (n := 12)
    (lo := (246615907 / 1000000000)) (hi := (61653977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819 / 640) = 1/(640 / 819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (246615907 / 1000000000) (61653977 / 250000000) (Real.log (819 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (819 / 640) = -Real.log (640 / 819) := by
    rw [show ((819 / 640) : ℝ) = ((640 / 819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (328070133 / 1000000000) ≤ -Real.log (461 / 640) ∧
    -Real.log (461 / 640) ≤ (164035067 / 500000000) := by
  have h := checkLog_sound (w := (179 / 1101)) (n := 12)
    (lo := (328070133 / 1000000000)) (hi := (164035067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 461) = 1/(461 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-164035067 / 500000000) (-328070133 / 1000000000) (Real.log (461 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2781477 / 6250000) ≤ -Real.log (512 / 799) ∧
    -Real.log (512 / 799) ≤ (445036321 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 1311)) (n := 12)
    (lo := (2781477 / 6250000)) (hi := (445036321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((799 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(799 / 512) = 1/(512 / 799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2781477 / 6250000) (445036321 / 1000000000) (Real.log (799 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (799 / 512) = -Real.log (512 / 799) := by
    rw [show ((799 / 512) : ℝ) = ((512 / 799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (411112111 / 500000000) ≤ -Real.log (225 / 512) ∧
    -Real.log (225 / 512) ≤ (25694507 / 31250000) := by
  have h := checkLog_sound (w := (31 / 481)) (n := 12)
    (lo := (64538521 / 500000000)) (hi := (129077043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 225) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 225) = 1/(225 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-25694507 / 31250000) (-411112111 / 500000000) (Real.log (225 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (444285099 / 1000000000) ≤ -Real.log (320 / 499) ∧
    -Real.log (320 / 499) ≤ (4442851 / 10000000) := by
  have h := checkLog_sound (w := (179 / 819)) (n := 12)
    (lo := (444285099 / 1000000000)) (hi := (4442851 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 320) = 1/(320 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (444285099 / 1000000000) (4442851 / 10000000) (Real.log (499 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (499 / 320) = -Real.log (320 / 499) := by
    rw [show ((499 / 320) : ℝ) = ((320 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (51222569 / 62500000) ≤ -Real.log (141 / 320) ∧
    -Real.log (141 / 320) ≤ (409780553 / 500000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 141) = 1/(141 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-409780553 / 500000000) (-51222569 / 62500000) (Real.log (141 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (337546659 / 1000000000) ≤ -Real.log (200000 / 280301) ∧
    -Real.log (200000 / 280301) ≤ (16877333 / 50000000) := by
  have h := checkLog_sound (w := (80301 / 480301)) (n := 12)
    (lo := (337546659 / 1000000000)) (hi := (16877333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280301 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(280301 / 200000) = 1/(200000 / 280301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (337546659 / 1000000000) (16877333 / 50000000) (Real.log (280301 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (280301 / 200000) = -Real.log (200000 / 280301) := by
    rw [show ((280301 / 200000) : ℝ) = ((200000 / 280301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (128334277 / 250000000) ≤ -Real.log (119699 / 200000) ∧
    -Real.log (119699 / 200000) ≤ (513337109 / 1000000000) := by
  have h := checkLog_sound (w := (80301 / 319699)) (n := 12)
    (lo := (128334277 / 250000000)) (hi := (513337109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 119699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 119699) = 1/(119699 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-513337109 / 1000000000) (-128334277 / 250000000) (Real.log (119699 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16908397 / 50000000) ≤ -Real.log (125000 / 175297) ∧
    -Real.log (125000 / 175297) ≤ (338167941 / 1000000000) := by
  have h := checkLog_sound (w := (50297 / 300297)) (n := 12)
    (lo := (16908397 / 50000000)) (hi := (338167941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175297 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175297 / 125000) = 1/(125000 / 175297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16908397 / 50000000) (338167941 / 1000000000) (Real.log (175297 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (175297 / 125000) = -Real.log (125000 / 175297) := by
    rw [show ((175297 / 125000) : ℝ) = ((125000 / 175297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (102958697 / 200000000) ≤ -Real.log (74703 / 125000) ∧
    -Real.log (74703 / 125000) ≤ (257396743 / 500000000) := by
  have h := checkLog_sound (w := (50297 / 199703)) (n := 12)
    (lo := (102958697 / 200000000)) (hi := (257396743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 74703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 74703) = 1/(74703 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-257396743 / 500000000) (-102958697 / 200000000) (Real.log (74703 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (260168779 / 1000000000) ≤ -Real.log (1000000 / 1297149) ∧
    -Real.log (1000000 / 1297149) ≤ (13008439 / 50000000) := by
  have h := checkLog_sound (w := (297149 / 2297149)) (n := 12)
    (lo := (260168779 / 1000000000)) (hi := (13008439 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297149 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1297149 / 1000000) = 1/(1000000 / 1297149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (260168779 / 1000000000) (13008439 / 50000000) (Real.log (1297149 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1297149 / 1000000) = -Real.log (1000000 / 1297149) := by
    rw [show ((1297149 / 1000000) : ℝ) = ((1000000 / 1297149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (176305179 / 500000000) ≤ -Real.log (702851 / 1000000) ∧
    -Real.log (702851 / 1000000) ≤ (352610359 / 1000000000) := by
  have h := checkLog_sound (w := (297149 / 1702851)) (n := 12)
    (lo := (176305179 / 500000000)) (hi := (352610359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 702851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 702851) = 1/(702851 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-352610359 / 1000000000) (-176305179 / 500000000) (Real.log (702851 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (260712131 / 1000000000) ≤ -Real.log (500000 / 648927) ∧
    -Real.log (500000 / 648927) ≤ (65178033 / 250000000) := by
  have h := checkLog_sound (w := (148927 / 1148927)) (n := 12)
    (lo := (260712131 / 1000000000)) (hi := (65178033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648927 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(648927 / 500000) = 1/(500000 / 648927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (260712131 / 1000000000) (65178033 / 250000000) (Real.log (648927 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (648927 / 500000) = -Real.log (500000 / 648927) := by
    rw [show ((648927 / 500000) : ℝ) = ((500000 / 648927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (353613919 / 1000000000) ≤ -Real.log (351073 / 500000) ∧
    -Real.log (351073 / 500000) ≤ (2210087 / 6250000) := by
  have h := checkLog_sound (w := (148927 / 851073)) (n := 12)
    (lo := (353613919 / 1000000000)) (hi := (2210087 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 351073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 351073) = 1/(351073 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2210087 / 6250000) (-353613919 / 1000000000) (Real.log (351073 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (425441883 / 500000000) ≤ -Real.log (250000000000 / 585428867409) ∧
    -Real.log (250000000000 / 585428867409) ≤ (106360471 / 125000000) := by
  have h := checkLog_sound (w := (85428867409 / 1085428867409)) (n := 12)
    (lo := (78868293 / 500000000)) (hi := (157736587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585428867409 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(585428867409 / 500000000000) = 1/(250000000000 / 585428867409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (425441883 / 500000000) (106360471 / 125000000) (Real.log (585428867409 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (585428867409 / 250000000000) = -Real.log (250000000000 / 585428867409) := by
    rw [show ((585428867409 / 250000000000) : ℝ) = ((250000000000 / 585428867409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (34118457 / 40000000) ≤ -Real.log (500000000000 / 1173292906577) ∧
    -Real.log (500000000000 / 1173292906577) ≤ (852961427 / 1000000000) := by
  have h := checkLog_sound (w := (173292906577 / 2173292906577)) (n := 12)
    (lo := (31962849 / 200000000)) (hi := (79907123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1173292906577 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1173292906577 / 1000000000000) = 1/(500000000000 / 1173292906577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (34118457 / 40000000) (852961427 / 1000000000) (Real.log (1173292906577 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1173292906577 / 500000000000) = -Real.log (500000000000 / 1173292906577) := by
    rw [show ((1173292906577 / 500000000000) : ℝ) = ((500000000000 / 1173292906577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (612779137 / 1000000000) ≤ -Real.log (250000000000 / 461388331239) ∧
    -Real.log (250000000000 / 461388331239) ≤ (306389569 / 500000000) := by
  have h := checkLog_sound (w := (211388331239 / 711388331239)) (n := 12)
    (lo := (612779137 / 1000000000)) (hi := (306389569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461388331239 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461388331239 / 250000000000) = 1/(250000000000 / 461388331239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (612779137 / 1000000000) (306389569 / 500000000) (Real.log (461388331239 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (461388331239 / 250000000000) = -Real.log (250000000000 / 461388331239) := by
    rw [show ((461388331239 / 250000000000) : ℝ) = ((250000000000 / 461388331239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (12286521 / 20000000) ≤ -Real.log (125000000000 / 231051305569) ∧
    -Real.log (125000000000 / 231051305569) ≤ (614326051 / 1000000000) := by
  have h := checkLog_sound (w := (106051305569 / 356051305569)) (n := 12)
    (lo := (12286521 / 20000000)) (hi := (614326051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231051305569 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231051305569 / 125000000000) = 1/(125000000000 / 231051305569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (12286521 / 20000000) (614326051 / 1000000000) (Real.log (231051305569 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (231051305569 / 125000000000) = -Real.log (125000000000 / 231051305569) := by
    rw [show ((231051305569 / 125000000000) : ℝ) = ((125000000000 / 231051305569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0241

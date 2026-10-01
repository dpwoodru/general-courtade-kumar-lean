import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0019
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

theorem reflection_log_1_neg : (136394337 / 200000000) ≤ -Real.log (25600 / 50631) ∧
    -Real.log (25600 / 50631) ≤ (340985843 / 500000000) := by
  have h := checkLog_sound (w := (25031 / 76231)) (n := 12)
    (lo := (136394337 / 200000000)) (hi := (340985843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50631 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50631 / 25600) = 1/(25600 / 50631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (136394337 / 200000000) (340985843 / 500000000) (Real.log (50631 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50631 / 25600) = -Real.log (25600 / 50631) := by
    rw [show ((50631 / 25600) : ℝ) = ((25600 / 50631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3806467193 / 1000000000) ≤ -Real.log (569 / 25600) ∧
    -Real.log (569 / 25600) ≤ (3806467199 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 1369)) (n := 12)
    (lo := (340731293 / 1000000000)) (hi := (170365647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 569) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 569) = 1/(569 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3806467199 / 1000000000) (-3806467193 / 1000000000) (Real.log (569 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (85234733 / 125000000) ≤ -Real.log (20480 / 40501) ∧
    -Real.log (20480 / 40501) ≤ (136375573 / 200000000) := by
  have h := checkLog_sound (w := (20021 / 60981)) (n := 12)
    (lo := (85234733 / 125000000)) (hi := (136375573 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40501 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40501 / 20480) = 1/(20480 / 40501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (85234733 / 125000000) (136375573 / 200000000) (Real.log (40501 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (40501 / 20480) = -Real.log (20480 / 40501) := by
    rw [show ((40501 / 20480) : ℝ) = ((20480 / 40501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1899076933 / 500000000) ≤ -Real.log (459 / 20480) ∧
    -Real.log (459 / 20480) ≤ (237384617 / 62500000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 459) = 1/(459 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-237384617 / 62500000) (-1899076933 / 500000000) (Real.log (459 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (134133977 / 200000000) ≤ -Real.log (12800 / 25031) ∧
    -Real.log (12800 / 25031) ≤ (335334943 / 500000000) := by
  have h := checkLog_sound (w := (12231 / 37831)) (n := 12)
    (lo := (134133977 / 200000000)) (hi := (335334943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25031 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25031 / 12800) = 1/(12800 / 25031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (134133977 / 200000000) (335334943 / 500000000) (Real.log (25031 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (25031 / 12800) = -Real.log (12800 / 25031) := by
    rw [show ((25031 / 12800) : ℝ) = ((12800 / 25031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3113320013 / 1000000000) ≤ -Real.log (569 / 12800) ∧
    -Real.log (569 / 12800) ≤ (1556660009 / 500000000) := by
  have h := checkLog_sound (w := (231 / 1369)) (n := 12)
    (lo := (340731293 / 1000000000)) (hi := (170365647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 569) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 569) = 1/(569 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1556660009 / 500000000) (-3113320013 / 1000000000) (Real.log (569 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (670480103 / 1000000000) ≤ -Real.log (10240 / 20021) ∧
    -Real.log (10240 / 20021) ≤ (83810013 / 125000000) := by
  have h := checkLog_sound (w := (9781 / 30261)) (n := 12)
    (lo := (670480103 / 1000000000)) (hi := (83810013 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20021 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20021 / 10240) = 1/(10240 / 20021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (670480103 / 1000000000) (83810013 / 125000000) (Real.log (20021 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (20021 / 10240) = -Real.log (10240 / 20021) := by
    rw [show ((20021 / 10240) : ℝ) = ((10240 / 20021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1552503343 / 500000000) ≤ -Real.log (459 / 10240) ∧
    -Real.log (459 / 10240) ≤ (3105006691 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 459) = 1/(459 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3105006691 / 1000000000) (-1552503343 / 500000000) (Real.log (459 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42725773 / 62500000) ≤ -Real.log (1000000 / 1981021) ∧
    -Real.log (1000000 / 1981021) ≤ (683612369 / 1000000000) := by
  have h := checkLog_sound (w := (981021 / 2981021)) (n := 12)
    (lo := (42725773 / 62500000)) (hi := (683612369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981021 / 1000000) = 1/(1000000 / 1981021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42725773 / 62500000) (683612369 / 1000000000) (Real.log (1981021 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1981021 / 1000000) = -Real.log (1000000 / 1981021) := by
    rw [show ((1981021 / 1000000) : ℝ) = ((1000000 / 1981021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3964422171 / 1000000000) ≤ -Real.log (18979 / 1000000) ∧
    -Real.log (18979 / 1000000) ≤ (3964422177 / 1000000000) := by
  have h := checkLog_sound (w := (12271 / 50229)) (n := 12)
    (lo := (498686271 / 1000000000)) (hi := (7791973 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18979) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18979) = 1/(18979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3964422177 / 1000000000) (-3964422171 / 1000000000) (Real.log (18979 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170922147 / 250000000) ≤ -Real.log (250000 / 495293) ∧
    -Real.log (250000 / 495293) ≤ (683688589 / 1000000000) := by
  have h := checkLog_sound (w := (245293 / 745293)) (n := 12)
    (lo := (170922147 / 250000000)) (hi := (683688589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495293 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495293 / 250000) = 1/(250000 / 495293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170922147 / 250000000) (683688589 / 1000000000) (Real.log (495293 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (495293 / 250000) = -Real.log (250000 / 495293) := by
    rw [show ((495293 / 250000) : ℝ) = ((250000 / 495293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (496551269 / 125000000) ≤ -Real.log (4707 / 250000) ∧
    -Real.log (4707 / 250000) ≤ (1986205079 / 500000000) := by
  have h := checkLog_sound (w := (6211 / 25039)) (n := 12)
    (lo := (126668563 / 250000000)) (hi := (506674253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9414) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9414) = 1/(4707 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1986205079 / 500000000) (-496551269 / 125000000) (Real.log (4707 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (42723249 / 62500000) ≤ -Real.log (1000000 / 1980941) ∧
    -Real.log (1000000 / 1980941) ≤ (136714397 / 200000000) := by
  have h := checkLog_sound (w := (980941 / 2980941)) (n := 12)
    (lo := (42723249 / 62500000)) (hi := (136714397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980941 / 1000000) = 1/(1000000 / 1980941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (42723249 / 62500000) (136714397 / 200000000) (Real.log (1980941 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1980941 / 1000000) = -Real.log (1000000 / 1980941) := by
    rw [show ((1980941 / 1000000) : ℝ) = ((1000000 / 1980941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (792043169 / 200000000) ≤ -Real.log (19059 / 1000000) ∧
    -Real.log (19059 / 1000000) ≤ (3960215851 / 1000000000) := by
  have h := checkLog_sound (w := (12191 / 50309)) (n := 12)
    (lo := (98895989 / 200000000)) (hi := (247239973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19059) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19059) = 1/(19059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3960215851 / 1000000000) (-792043169 / 200000000) (Real.log (19059 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (341824861 / 500000000) ≤ -Real.log (200000 / 396219) ∧
    -Real.log (200000 / 396219) ≤ (683649723 / 1000000000) := by
  have h := checkLog_sound (w := (196219 / 596219)) (n := 12)
    (lo := (341824861 / 500000000)) (hi := (683649723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396219 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396219 / 200000) = 1/(200000 / 396219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (341824861 / 500000000) (683649723 / 1000000000) (Real.log (396219 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (396219 / 200000) = -Real.log (200000 / 396219) := by
    rw [show ((396219 / 200000) : ℝ) = ((200000 / 396219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1984164419 / 500000000) ≤ -Real.log (3781 / 200000) ∧
    -Real.log (3781 / 200000) ≤ (992082211 / 250000000) := by
  have h := checkLog_sound (w := (2469 / 10031)) (n := 12)
    (lo := (251296469 / 500000000)) (hi := (502592939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3781) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3781) = 1/(3781 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-992082211 / 250000000) (-1984164419 / 500000000) (Real.log (3781 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4648034539 / 1000000000) ≤ -Real.log (500000000000 / 52189815058749) ∧
    -Real.log (500000000000 / 52189815058749) ≤ (2324017273 / 500000000) := by
  have h := checkLog_sound (w := (20189815058749 / 84189815058749)) (n := 12)
    (lo := (489151459 / 1000000000)) (hi := (24457573 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52189815058749 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52189815058749 / 32000000000000) = 1/(500000000000 / 52189815058749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4648034539 / 1000000000) (2324017273 / 500000000) (Real.log (52189815058749 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (52189815058749 / 500000000000) = -Real.log (500000000000 / 52189815058749) := by
    rw [show ((52189815058749 / 500000000000) : ℝ) = ((500000000000 / 52189815058749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (232804937 / 50000000) ≤ -Real.log (500000000000 / 52612385808371) ∧
    -Real.log (500000000000 / 52612385808371) ≤ (4656098747 / 1000000000) := by
  have h := checkLog_sound (w := (20612385808371 / 84612385808371)) (n := 12)
    (lo := (24860783 / 50000000)) (hi := (497215661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52612385808371 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52612385808371 / 32000000000000) = 1/(500000000000 / 52612385808371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (232804937 / 50000000) (4656098747 / 1000000000) (Real.log (52612385808371 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (52612385808371 / 500000000000) = -Real.log (500000000000 / 52612385808371) := by
    rw [show ((52612385808371 / 500000000000) : ℝ) = ((500000000000 / 52612385808371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4643787829 / 1000000000) ≤ -Real.log (100000000000 / 10393729996327) ∧
    -Real.log (100000000000 / 10393729996327) ≤ (1160946959 / 250000000) := by
  have h := checkLog_sound (w := (3993729996327 / 16793729996327)) (n := 12)
    (lo := (484904749 / 1000000000)) (hi := (1939619 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10393729996327 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10393729996327 / 6400000000000) = 1/(100000000000 / 10393729996327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4643787829 / 1000000000) (1160946959 / 250000000) (Real.log (10393729996327 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10393729996327 / 100000000000) = -Real.log (100000000000 / 10393729996327) := by
    rw [show ((10393729996327 / 100000000000) : ℝ) = ((100000000000 / 10393729996327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (14537433 / 3125000) ≤ -Real.log (500000000000 / 52396059243587) ∧
    -Real.log (500000000000 / 52396059243587) ≤ (4651978567 / 1000000000) := by
  have h := checkLog_sound (w := (20396059243587 / 84396059243587)) (n := 12)
    (lo := (12327387 / 25000000)) (hi := (493095481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52396059243587 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52396059243587 / 32000000000000) = 1/(500000000000 / 52396059243587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (14537433 / 3125000) (4651978567 / 1000000000) (Real.log (52396059243587 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (52396059243587 / 500000000000) = -Real.log (500000000000 / 52396059243587) := by
    rw [show ((52396059243587 / 500000000000) : ℝ) = ((500000000000 / 52396059243587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0019

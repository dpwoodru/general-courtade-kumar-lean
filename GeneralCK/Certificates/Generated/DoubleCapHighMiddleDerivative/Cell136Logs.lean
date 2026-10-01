import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell136
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (285384513 / 1000000000) ≤ -Real.log (5120 / 6811) ∧
    -Real.log (5120 / 6811) ≤ (142692257 / 500000000) := by
  have h := checkLog_sound (w := (1691 / 11931)) (n := 12)
    (lo := (285384513 / 1000000000)) (hi := (142692257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6811 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6811 / 5120) = 1/(5120 / 6811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (285384513 / 1000000000) (142692257 / 500000000) (Real.log (6811 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6811 / 5120) = -Real.log (5120 / 6811) := by
    rw [show ((6811 / 5120) : ℝ) = ((5120 / 6811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (80177153 / 200000000) ≤ -Real.log (3429 / 5120) ∧
    -Real.log (3429 / 5120) ≤ (200442883 / 500000000) := by
  have h := checkLog_sound (w := (1691 / 8549)) (n := 12)
    (lo := (80177153 / 200000000)) (hi := (200442883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3429) = 1/(3429 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-200442883 / 500000000) (-80177153 / 200000000) (Real.log (3429 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (17808997 / 62500000) ≤ -Real.log (640 / 851) ∧
    -Real.log (640 / 851) ≤ (284943953 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1491)) (n := 12)
    (lo := (17808997 / 62500000)) (hi := (284943953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851 / 640) = 1/(640 / 851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (17808997 / 62500000) (284943953 / 1000000000) (Real.log (851 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (851 / 640) = -Real.log (640 / 851) := by
    rw [show ((851 / 640) : ℝ) = ((640 / 851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (400011257 / 1000000000) ≤ -Real.log (429 / 640) ∧
    -Real.log (429 / 640) ≤ (200005629 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 429) = 1/(429 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-200005629 / 500000000) (-400011257 / 1000000000) (Real.log (429 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (210447293 / 1000000000) ≤ -Real.log (100000 / 123423) ∧
    -Real.log (100000 / 123423) ≤ (105223647 / 500000000) := by
  have h := checkLog_sound (w := (23423 / 223423)) (n := 12)
    (lo := (210447293 / 1000000000)) (hi := (105223647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123423 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123423 / 100000) = 1/(100000 / 123423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (210447293 / 1000000000) (105223647 / 500000000) (Real.log (123423 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (123423 / 100000) = -Real.log (100000 / 123423) := by
    rw [show ((123423 / 100000) : ℝ) = ((100000 / 123423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (53374683 / 200000000) ≤ -Real.log (76577 / 100000) ∧
    -Real.log (76577 / 100000) ≤ (33359177 / 125000000) := by
  have h := checkLog_sound (w := (23423 / 176577)) (n := 12)
    (lo := (53374683 / 200000000)) (hi := (33359177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76577) = 1/(76577 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-33359177 / 125000000) (-53374683 / 200000000) (Real.log (76577 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (210788339 / 1000000000) ≤ -Real.log (1000000 / 1234651) ∧
    -Real.log (1000000 / 1234651) ≤ (10539417 / 50000000) := by
  have h := checkLog_sound (w := (234651 / 2234651)) (n := 12)
    (lo := (210788339 / 1000000000)) (hi := (10539417 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1234651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1234651 / 1000000) = 1/(1000000 / 1234651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (210788339 / 1000000000) (10539417 / 50000000) (Real.log (1234651 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1234651 / 1000000) = -Real.log (1000000 / 1234651) := by
    rw [show ((1234651 / 1000000) : ℝ) = ((1000000 / 1234651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (13371167 / 50000000) ≤ -Real.log (765349 / 1000000) ∧
    -Real.log (765349 / 1000000) ≤ (267423341 / 1000000000) := by
  have h := checkLog_sound (w := (234651 / 1765349)) (n := 12)
    (lo := (13371167 / 50000000)) (hi := (267423341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 765349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 765349) = 1/(765349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-267423341 / 1000000000) (-13371167 / 50000000) (Real.log (765349 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (77724347 / 500000000) ≤ -Real.log (500000 / 584091) ∧
    -Real.log (500000 / 584091) ≤ (31089739 / 200000000) := by
  have h := checkLog_sound (w := (84091 / 1084091)) (n := 12)
    (lo := (77724347 / 500000000)) (hi := (31089739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584091 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584091 / 500000) = 1/(500000 / 584091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (77724347 / 500000000) (31089739 / 200000000) (Real.log (584091 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (584091 / 500000) = -Real.log (500000 / 584091) := by
    rw [show ((584091 / 500000) : ℝ) = ((500000 / 584091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (46035403 / 250000000) ≤ -Real.log (415909 / 500000) ∧
    -Real.log (415909 / 500000) ≤ (184141613 / 1000000000) := by
  have h := checkLog_sound (w := (84091 / 915909)) (n := 12)
    (lo := (46035403 / 250000000)) (hi := (184141613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415909) = 1/(415909 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-184141613 / 1000000000) (-46035403 / 250000000) (Real.log (415909 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7785787 / 50000000) ≤ -Real.log (500000 / 584247) ∧
    -Real.log (500000 / 584247) ≤ (155715741 / 1000000000) := by
  have h := checkLog_sound (w := (84247 / 1084247)) (n := 12)
    (lo := (7785787 / 50000000)) (hi := (155715741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584247 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584247 / 500000) = 1/(500000 / 584247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7785787 / 50000000) (155715741 / 1000000000) (Real.log (584247 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (584247 / 500000) = -Real.log (500000 / 584247) := by
    rw [show ((584247 / 500000) : ℝ) = ((500000 / 584247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (46129191 / 250000000) ≤ -Real.log (415753 / 500000) ∧
    -Real.log (415753 / 500000) ≤ (36903353 / 200000000) := by
  have h := checkLog_sound (w := (84247 / 915753)) (n := 12)
    (lo := (46129191 / 250000000)) (hi := (36903353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415753) = 1/(415753 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36903353 / 200000000) (-46129191 / 250000000) (Real.log (415753 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684955209 / 1000000000) ≤ -Real.log (500000000000 / 991841491841) ∧
    -Real.log (500000000000 / 991841491841) ≤ (68495521 / 100000000) := by
  have h := checkLog_sound (w := (491841491841 / 1491841491841)) (n := 12)
    (lo := (684955209 / 1000000000)) (hi := (68495521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991841491841 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991841491841 / 500000000000) = 1/(500000000000 / 991841491841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684955209 / 1000000000) (68495521 / 100000000) (Real.log (991841491841 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (991841491841 / 500000000000) = -Real.log (500000000000 / 991841491841) := by
    rw [show ((991841491841 / 500000000000) : ℝ) = ((500000000000 / 991841491841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (343135139 / 500000000) ≤ -Real.log (250000000000 / 496573344999) ∧
    -Real.log (250000000000 / 496573344999) ≤ (686270279 / 1000000000) := by
  have h := checkLog_sound (w := (246573344999 / 746573344999)) (n := 12)
    (lo := (343135139 / 500000000)) (hi := (686270279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((496573344999 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(496573344999 / 250000000000) = 1/(250000000000 / 496573344999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (343135139 / 500000000) (686270279 / 1000000000) (Real.log (496573344999 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (496573344999 / 250000000000) = -Real.log (250000000000 / 496573344999) := by
    rw [show ((496573344999 / 250000000000) : ℝ) = ((250000000000 / 496573344999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (477320709 / 1000000000) ≤ -Real.log (500000000000 / 805875132219) ∧
    -Real.log (500000000000 / 805875132219) ≤ (47732071 / 100000000) := by
  have h := checkLog_sound (w := (305875132219 / 1305875132219)) (n := 12)
    (lo := (477320709 / 1000000000)) (hi := (47732071 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805875132219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805875132219 / 500000000000) = 1/(500000000000 / 805875132219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (477320709 / 1000000000) (47732071 / 100000000) (Real.log (805875132219 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (805875132219 / 500000000000) = -Real.log (500000000000 / 805875132219) := by
    rw [show ((805875132219 / 500000000000) : ℝ) = ((500000000000 / 805875132219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (478211679 / 1000000000) ≤ -Real.log (500000000000 / 806593462591) ∧
    -Real.log (500000000000 / 806593462591) ≤ (2988823 / 6250000) := by
  have h := checkLog_sound (w := (306593462591 / 1306593462591)) (n := 12)
    (lo := (478211679 / 1000000000)) (hi := (2988823 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((806593462591 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(806593462591 / 500000000000) = 1/(500000000000 / 806593462591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (478211679 / 1000000000) (2988823 / 6250000) (Real.log (806593462591 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (806593462591 / 500000000000) = -Real.log (500000000000 / 806593462591) := by
    rw [show ((806593462591 / 500000000000) : ℝ) = ((500000000000 / 806593462591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (169795153 / 500000000) ≤ -Real.log (250000000000 / 351093027561) ∧
    -Real.log (250000000000 / 351093027561) ≤ (339590307 / 1000000000) := by
  have h := checkLog_sound (w := (101093027561 / 601093027561)) (n := 12)
    (lo := (169795153 / 500000000)) (hi := (339590307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351093027561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351093027561 / 250000000000) = 1/(250000000000 / 351093027561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (169795153 / 500000000) (339590307 / 1000000000) (Real.log (351093027561 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (351093027561 / 250000000000) = -Real.log (250000000000 / 351093027561) := by
    rw [show ((351093027561 / 250000000000) : ℝ) = ((250000000000 / 351093027561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (42529063 / 125000000) ≤ -Real.log (500000000000 / 702637142727) ∧
    -Real.log (500000000000 / 702637142727) ≤ (68046501 / 200000000) := by
  have h := checkLog_sound (w := (202637142727 / 1202637142727)) (n := 12)
    (lo := (42529063 / 125000000)) (hi := (68046501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702637142727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702637142727 / 500000000000) = 1/(500000000000 / 702637142727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (42529063 / 125000000) (68046501 / 200000000) (Real.log (702637142727 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (702637142727 / 500000000000) = -Real.log (500000000000 / 702637142727) := by
    rw [show ((702637142727 / 500000000000) : ℝ) = ((500000000000 / 702637142727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (56252 / 1953125) ≤ -Real.log (242902442991 / 250000000000) ∧
    -Real.log (242902442991 / 250000000000) ≤ (1152041 / 40000000) := by
  have h := checkLog_sound (w := (7097557009 / 492902442991)) (n := 12)
    (lo := (56252 / 1953125)) (hi := (1152041 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242902442991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242902442991) = 1/(242902442991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1152041 / 40000000) (-56252 / 1953125) (Real.log (242902442991 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (28692917 / 1000000000) ≤ -Real.log (242928703719 / 250000000000) ∧
    -Real.log (242928703719 / 250000000000) ≤ (14346459 / 500000000) := by
  have h := checkLog_sound (w := (7071296281 / 492928703719)) (n := 12)
    (lo := (28692917 / 1000000000)) (hi := (14346459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242928703719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242928703719) = 1/(242928703719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-14346459 / 500000000) (-28692917 / 1000000000) (Real.log (242928703719 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell136

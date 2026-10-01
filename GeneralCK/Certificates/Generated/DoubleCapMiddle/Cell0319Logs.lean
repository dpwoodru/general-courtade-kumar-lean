import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0319
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

theorem reflection_log_1_neg : (109732459 / 500000000) ≤ -Real.log (10240 / 12753) ∧
    -Real.log (10240 / 12753) ≤ (219464919 / 1000000000) := by
  have h := checkLog_sound (w := (2513 / 22993)) (n := 12)
    (lo := (109732459 / 500000000)) (hi := (219464919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12753 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12753 / 10240) = 1/(10240 / 12753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (109732459 / 500000000) (219464919 / 1000000000) (Real.log (12753 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12753 / 10240) = -Real.log (10240 / 12753) := by
    rw [show ((12753 / 10240) : ℝ) = ((10240 / 12753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (28158093 / 100000000) ≤ -Real.log (7727 / 10240) ∧
    -Real.log (7727 / 10240) ≤ (281580931 / 1000000000) := by
  have h := checkLog_sound (w := (2513 / 17967)) (n := 12)
    (lo := (28158093 / 100000000)) (hi := (281580931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7727) = 1/(7727 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-281580931 / 1000000000) (-28158093 / 100000000) (Real.log (7727 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (219229651 / 1000000000) ≤ -Real.log (1024 / 1275) ∧
    -Real.log (1024 / 1275) ≤ (54807413 / 250000000) := by
  have h := checkLog_sound (w := (251 / 2299)) (n := 12)
    (lo := (219229651 / 1000000000)) (hi := (54807413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275 / 1024) = 1/(1024 / 1275) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (219229651 / 1000000000) (54807413 / 250000000) (Real.log (1275 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1275 / 1024) = -Real.log (1024 / 1275) := by
    rw [show ((1275 / 1024) : ℝ) = ((1024 / 1275) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (281192757 / 1000000000) ≤ -Real.log (773 / 1024) ∧
    -Real.log (773 / 1024) ≤ (140596379 / 500000000) := by
  have h := checkLog_sound (w := (251 / 1797)) (n := 12)
    (lo := (281192757 / 1000000000)) (hi := (140596379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 773) = 1/(773 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-140596379 / 500000000) (-281192757 / 1000000000) (Real.log (773 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (399326513 / 1000000000) ≤ -Real.log (5120 / 7633) ∧
    -Real.log (5120 / 7633) ≤ (199663257 / 500000000) := by
  have h := checkLog_sound (w := (2513 / 12753)) (n := 12)
    (lo := (399326513 / 1000000000)) (hi := (199663257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7633 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7633 / 5120) = 1/(5120 / 7633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (399326513 / 1000000000) (199663257 / 500000000) (Real.log (7633 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7633 / 5120) = -Real.log (5120 / 7633) := by
    rw [show ((7633 / 5120) : ℝ) = ((5120 / 7633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10546161 / 15625000) ≤ -Real.log (2607 / 5120) ∧
    -Real.log (2607 / 5120) ≤ (134990861 / 200000000) := by
  have h := checkLog_sound (w := (2513 / 7727)) (n := 12)
    (lo := (10546161 / 15625000)) (hi := (134990861 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2607) = 1/(2607 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-134990861 / 200000000) (-10546161 / 15625000) (Real.log (2607 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (199466703 / 500000000) ≤ -Real.log (512 / 763) ∧
    -Real.log (512 / 763) ≤ (398933407 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 1275)) (n := 12)
    (lo := (199466703 / 500000000)) (hi := (398933407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((763 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(763 / 512) = 1/(512 / 763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (199466703 / 500000000) (398933407 / 1000000000) (Real.log (763 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (763 / 512) = -Real.log (512 / 763) := by
    rw [show ((763 / 512) : ℝ) = ((512 / 763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (673804217 / 1000000000) ≤ -Real.log (261 / 512) ∧
    -Real.log (261 / 512) ≤ (336902109 / 500000000) := by
  have h := checkLog_sound (w := (251 / 773)) (n := 12)
    (lo := (673804217 / 1000000000)) (hi := (336902109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 261) = 1/(261 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-336902109 / 500000000) (-673804217 / 1000000000) (Real.log (261 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (150243741 / 500000000) ≤ -Real.log (1000000 / 1350517) ∧
    -Real.log (1000000 / 1350517) ≤ (300487483 / 1000000000) := by
  have h := checkLog_sound (w := (350517 / 2350517)) (n := 12)
    (lo := (150243741 / 500000000)) (hi := (300487483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1350517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1350517 / 1000000) = 1/(1000000 / 1350517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (150243741 / 500000000) (300487483 / 1000000000) (Real.log (1350517 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1350517 / 1000000) = -Real.log (1000000 / 1350517) := by
    rw [show ((1350517 / 1000000) : ℝ) = ((1000000 / 1350517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (431578617 / 1000000000) ≤ -Real.log (649483 / 1000000) ∧
    -Real.log (649483 / 1000000) ≤ (215789309 / 500000000) := by
  have h := checkLog_sound (w := (350517 / 1649483)) (n := 12)
    (lo := (431578617 / 1000000000)) (hi := (215789309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 649483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 649483) = 1/(649483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-215789309 / 500000000) (-431578617 / 1000000000) (Real.log (649483 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37600821 / 125000000) ≤ -Real.log (250000 / 337737) ∧
    -Real.log (250000 / 337737) ≤ (300806569 / 1000000000) := by
  have h := checkLog_sound (w := (87737 / 587737)) (n := 12)
    (lo := (37600821 / 125000000)) (hi := (300806569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337737 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(337737 / 250000) = 1/(250000 / 337737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37600821 / 125000000) (300806569 / 1000000000) (Real.log (337737 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (337737 / 250000) = -Real.log (250000 / 337737) := by
    rw [show ((337737 / 250000) : ℝ) = ((250000 / 337737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (216121221 / 500000000) ≤ -Real.log (162263 / 250000) ∧
    -Real.log (162263 / 250000) ≤ (432242443 / 1000000000) := by
  have h := checkLog_sound (w := (87737 / 412263)) (n := 12)
    (lo := (216121221 / 500000000)) (hi := (432242443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 162263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 162263) = 1/(162263 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-432242443 / 1000000000) (-216121221 / 500000000) (Real.log (162263 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45677953 / 200000000) ≤ -Real.log (40000 / 50263) ∧
    -Real.log (40000 / 50263) ≤ (114194883 / 500000000) := by
  have h := checkLog_sound (w := (10263 / 90263)) (n := 12)
    (lo := (45677953 / 200000000)) (hi := (114194883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50263 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50263 / 40000) = 1/(40000 / 50263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45677953 / 200000000) (114194883 / 500000000) (Real.log (50263 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (50263 / 40000) = -Real.log (40000 / 50263) := by
    rw [show ((50263 / 40000) : ℝ) = ((40000 / 50263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (9265231 / 31250000) ≤ -Real.log (29737 / 40000) ∧
    -Real.log (29737 / 40000) ≤ (296487393 / 1000000000) := by
  have h := checkLog_sound (w := (10263 / 69737)) (n := 12)
    (lo := (9265231 / 31250000)) (hi := (296487393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 29737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 29737) = 1/(29737 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-296487393 / 1000000000) (-9265231 / 31250000) (Real.log (29737 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (114329357 / 500000000) ≤ -Real.log (1000000 / 1256913) ∧
    -Real.log (1000000 / 1256913) ≤ (45731743 / 200000000) := by
  have h := checkLog_sound (w := (256913 / 2256913)) (n := 12)
    (lo := (114329357 / 500000000)) (hi := (45731743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1256913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1256913 / 1000000) = 1/(1000000 / 1256913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (114329357 / 500000000) (45731743 / 200000000) (Real.log (1256913 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1256913 / 1000000) = -Real.log (1000000 / 1256913) := by
    rw [show ((1256913 / 1000000) : ℝ) = ((1000000 / 1256913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (74235537 / 250000000) ≤ -Real.log (743087 / 1000000) ∧
    -Real.log (743087 / 1000000) ≤ (296942149 / 1000000000) := by
  have h := checkLog_sound (w := (256913 / 1743087)) (n := 12)
    (lo := (74235537 / 250000000)) (hi := (296942149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 743087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 743087) = 1/(743087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-296942149 / 1000000000) (-74235537 / 250000000) (Real.log (743087 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (366033049 / 500000000) ≤ -Real.log (250000000000 / 519843090581) ∧
    -Real.log (250000000000 / 519843090581) ≤ (7320661 / 10000000) := by
  have h := checkLog_sound (w := (19843090581 / 1019843090581)) (n := 12)
    (lo := (19459459 / 500000000)) (hi := (38918919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((519843090581 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(519843090581 / 500000000000) = 1/(250000000000 / 519843090581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (366033049 / 500000000) (7320661 / 10000000) (Real.log (519843090581 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (519843090581 / 250000000000) = -Real.log (250000000000 / 519843090581) := by
    rw [show ((519843090581 / 250000000000) : ℝ) = ((250000000000 / 519843090581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (733049009 / 1000000000) ≤ -Real.log (500000000000 / 1040708602701) ∧
    -Real.log (500000000000 / 1040708602701) ≤ (733049011 / 1000000000) := by
  have h := checkLog_sound (w := (40708602701 / 2040708602701)) (n := 12)
    (lo := (39901829 / 1000000000)) (hi := (3990183 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1040708602701 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1040708602701 / 1000000000000) = 1/(500000000000 / 1040708602701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (733049009 / 1000000000) (733049011 / 1000000000) (Real.log (1040708602701 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1040708602701 / 500000000000) = -Real.log (500000000000 / 1040708602701) := by
    rw [show ((1040708602701 / 500000000000) : ℝ) = ((500000000000 / 1040708602701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (262438579 / 500000000) ≤ -Real.log (500000000000 / 845125601103) ∧
    -Real.log (500000000000 / 845125601103) ≤ (524877159 / 1000000000) := by
  have h := checkLog_sound (w := (345125601103 / 1345125601103)) (n := 12)
    (lo := (262438579 / 500000000)) (hi := (524877159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((845125601103 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(845125601103 / 500000000000) = 1/(500000000000 / 845125601103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (262438579 / 500000000) (524877159 / 1000000000) (Real.log (845125601103 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (845125601103 / 500000000000) = -Real.log (500000000000 / 845125601103) := by
    rw [show ((845125601103 / 500000000000) : ℝ) = ((500000000000 / 845125601103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (525600863 / 1000000000) ≤ -Real.log (250000000000 / 422868721967) ∧
    -Real.log (250000000000 / 422868721967) ≤ (16425027 / 31250000) := by
  have h := checkLog_sound (w := (172868721967 / 672868721967)) (n := 12)
    (lo := (525600863 / 1000000000)) (hi := (16425027 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422868721967 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422868721967 / 250000000000) = 1/(250000000000 / 422868721967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (525600863 / 1000000000) (16425027 / 31250000) (Real.log (422868721967 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (422868721967 / 250000000000) = -Real.log (250000000000 / 422868721967) := by
    rw [show ((422868721967 / 250000000000) : ℝ) = ((250000000000 / 422868721967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0319

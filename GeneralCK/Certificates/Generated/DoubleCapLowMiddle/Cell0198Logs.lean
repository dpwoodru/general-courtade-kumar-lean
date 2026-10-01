import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0198
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

theorem reflection_log_1_neg : (597031989 / 1000000000) ≤ -Real.log (6400 / 11627) ∧
    -Real.log (6400 / 11627) ≤ (59703199 / 100000000) := by
  have h := checkLog_sound (w := (5227 / 18027)) (n := 12)
    (lo := (597031989 / 1000000000)) (hi := (59703199 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11627 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11627 / 6400) = 1/(6400 / 11627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (597031989 / 1000000000) (59703199 / 100000000) (Real.log (11627 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11627 / 6400) = -Real.log (6400 / 11627) := by
    rw [show ((11627 / 6400) : ℝ) = ((6400 / 11627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1696733419 / 1000000000) ≤ -Real.log (1173 / 6400) ∧
    -Real.log (1173 / 6400) ≤ (848366711 / 500000000) := by
  have h := checkLog_sound (w := (427 / 2773)) (n := 12)
    (lo := (310439059 / 1000000000)) (hi := (15521953 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1173) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1173) = 1/(1173 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-848366711 / 500000000) (-1696733419 / 1000000000) (Real.log (1173 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (23815861 / 40000000) ≤ -Real.log (800 / 1451) ∧
    -Real.log (800 / 1451) ≤ (297698263 / 500000000) := by
  have h := checkLog_sound (w := (651 / 2251)) (n := 12)
    (lo := (23815861 / 40000000)) (hi := (297698263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 800) = 1/(800 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (23815861 / 40000000) (297698263 / 500000000) (Real.log (1451 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1451 / 800) = -Real.log (800 / 1451) := by
    rw [show ((1451 / 800) : ℝ) = ((800 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (84033271 / 50000000) ≤ -Real.log (149 / 800) ∧
    -Real.log (149 / 800) ≤ (1680665423 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 349)) (n := 12)
    (lo := (14718553 / 50000000)) (hi := (294371061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 149) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 149) = 1/(149 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1680665423 / 1000000000) (-84033271 / 50000000) (Real.log (149 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (490686689 / 1000000000) ≤ -Real.log (3200 / 5227) ∧
    -Real.log (3200 / 5227) ≤ (49068669 / 100000000) := by
  have h := checkLog_sound (w := (2027 / 8427)) (n := 12)
    (lo := (490686689 / 1000000000)) (hi := (49068669 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5227 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5227 / 3200) = 1/(3200 / 5227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (490686689 / 1000000000) (49068669 / 100000000) (Real.log (5227 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5227 / 3200) = -Real.log (3200 / 5227) := by
    rw [show ((5227 / 3200) : ℝ) = ((3200 / 5227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1003586239 / 1000000000) ≤ -Real.log (1173 / 3200) ∧
    -Real.log (1173 / 3200) ≤ (1003586241 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 2773)) (n := 12)
    (lo := (310439059 / 1000000000)) (hi := (15521953 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1173) = 1/(1173 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1003586241 / 1000000000) (-1003586239 / 1000000000) (Real.log (1173 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97409019 / 200000000) ≤ -Real.log (400 / 651) ∧
    -Real.log (400 / 651) ≤ (60880637 / 125000000) := by
  have h := checkLog_sound (w := (251 / 1051)) (n := 12)
    (lo := (97409019 / 200000000)) (hi := (60880637 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651 / 400) = 1/(400 / 651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97409019 / 200000000) (60880637 / 125000000) (Real.log (651 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (651 / 400) = -Real.log (400 / 651) := by
    rw [show ((651 / 400) : ℝ) = ((400 / 651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6171989 / 6250000) ≤ -Real.log (149 / 400) ∧
    -Real.log (149 / 400) ≤ (493759121 / 500000000) := by
  have h := checkLog_sound (w := (51 / 349)) (n := 12)
    (lo := (14718553 / 50000000)) (hi := (294371061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 149) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 149) = 1/(149 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-493759121 / 500000000) (-6171989 / 6250000) (Real.log (149 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (156498511 / 250000000) ≤ -Real.log (125000 / 233763) ∧
    -Real.log (125000 / 233763) ≤ (125198809 / 200000000) := by
  have h := checkLog_sound (w := (108763 / 358763)) (n := 12)
    (lo := (156498511 / 250000000)) (hi := (125198809 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233763 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233763 / 125000) = 1/(125000 / 233763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (156498511 / 250000000) (125198809 / 200000000) (Real.log (233763 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (233763 / 125000) = -Real.log (125000 / 233763) := by
    rw [show ((233763 / 125000) : ℝ) = ((125000 / 233763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2041021147 / 1000000000) ≤ -Real.log (16237 / 125000) ∧
    -Real.log (16237 / 125000) ≤ (40820423 / 20000000) := by
  have h := checkLog_sound (w := (15013 / 47487)) (n := 12)
    (lo := (654726787 / 1000000000)) (hi := (163681697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16237) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 16237) = 1/(16237 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-40820423 / 20000000) (-2041021147 / 1000000000) (Real.log (16237 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (19589857 / 31250000) ≤ -Real.log (1000000 / 1871753) ∧
    -Real.log (1000000 / 1871753) ≤ (25075017 / 40000000) := by
  have h := checkLog_sound (w := (871753 / 2871753)) (n := 12)
    (lo := (19589857 / 31250000)) (hi := (25075017 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1871753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1871753 / 1000000) = 1/(1000000 / 1871753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (19589857 / 31250000) (25075017 / 40000000) (Real.log (1871753 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1871753 / 1000000) = -Real.log (1000000 / 1871753) := by
    rw [show ((1871753 / 1000000) : ℝ) = ((1000000 / 1871753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (410759437 / 200000000) ≤ -Real.log (128247 / 1000000) ∧
    -Real.log (128247 / 1000000) ≤ (513449297 / 250000000) := by
  have h := checkLog_sound (w := (121753 / 378247)) (n := 12)
    (lo := (26700113 / 40000000)) (hi := (333751413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 128247) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 128247) = 1/(128247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-513449297 / 250000000) (-410759437 / 200000000) (Real.log (128247 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (124088629 / 200000000) ≤ -Real.log (125000 / 232469) ∧
    -Real.log (125000 / 232469) ≤ (310221573 / 500000000) := by
  have h := checkLog_sound (w := (107469 / 357469)) (n := 12)
    (lo := (124088629 / 200000000)) (hi := (310221573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232469 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(232469 / 125000) = 1/(125000 / 232469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (124088629 / 200000000) (310221573 / 500000000) (Real.log (232469 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (232469 / 125000) = -Real.log (125000 / 232469) := by
    rw [show ((232469 / 125000) : ℝ) = ((125000 / 232469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1964342993 / 1000000000) ≤ -Real.log (17531 / 125000) ∧
    -Real.log (17531 / 125000) ≤ (491085749 / 250000000) := by
  have h := checkLog_sound (w := (13719 / 48781)) (n := 12)
    (lo := (578048633 / 1000000000)) (hi := (289024317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17531) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 17531) = 1/(17531 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-491085749 / 250000000) (-1964342993 / 1000000000) (Real.log (17531 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (155385269 / 250000000) ≤ -Real.log (200000 / 372359) ∧
    -Real.log (200000 / 372359) ≤ (621541077 / 1000000000) := by
  have h := checkLog_sound (w := (172359 / 572359)) (n := 12)
    (lo := (155385269 / 250000000)) (hi := (621541077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372359 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372359 / 200000) = 1/(200000 / 372359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (155385269 / 250000000) (621541077 / 1000000000) (Real.log (372359 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (372359 / 200000) = -Real.log (200000 / 372359) := by
    rw [show ((372359 / 200000) : ℝ) = ((200000 / 372359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1979017187 / 1000000000) ≤ -Real.log (27641 / 200000) ∧
    -Real.log (27641 / 200000) ≤ (197901719 / 100000000) := by
  have h := checkLog_sound (w := (22359 / 77641)) (n := 12)
    (lo := (592722827 / 1000000000)) (hi := (148180707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 27641) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 27641) = 1/(27641 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-197901719 / 100000000) (-1979017187 / 1000000000) (Real.log (27641 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2667015191 / 1000000000) ≤ -Real.log (12500000000 / 179961661637) ∧
    -Real.log (12500000000 / 179961661637) ≤ (533403039 / 200000000) := by
  have h := checkLog_sound (w := (79961661637 / 279961661637)) (n := 12)
    (lo := (587573651 / 1000000000)) (hi := (146893413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179961661637 / 100000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(179961661637 / 100000000000) = 1/(12500000000 / 179961661637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2667015191 / 1000000000) (533403039 / 200000000) (Real.log (179961661637 / 12500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (179961661637 / 12500000000) = -Real.log (12500000000 / 179961661637) := by
    rw [show ((179961661637 / 12500000000) : ℝ) = ((12500000000 / 179961661637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (268067261 / 100000000) ≤ -Real.log (62500000000 / 912181668967) ∧
    -Real.log (62500000000 / 912181668967) ≤ (1340336307 / 500000000) := by
  have h := checkLog_sound (w := (412181668967 / 1412181668967)) (n := 12)
    (lo := (60123107 / 100000000)) (hi := (601231071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((912181668967 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(912181668967 / 500000000000) = 1/(62500000000 / 912181668967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (268067261 / 100000000) (1340336307 / 500000000) (Real.log (912181668967 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (912181668967 / 62500000000) = -Real.log (62500000000 / 912181668967) := by
    rw [show ((912181668967 / 62500000000) : ℝ) = ((62500000000 / 912181668967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1292393069 / 500000000) ≤ -Real.log (62500000000 / 828778306999) ∧
    -Real.log (62500000000 / 828778306999) ≤ (1292393071 / 500000000) := by
  have h := checkLog_sound (w := (328778306999 / 1328778306999)) (n := 12)
    (lo := (252672299 / 500000000)) (hi := (505344599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((828778306999 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(828778306999 / 500000000000) = 1/(62500000000 / 828778306999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1292393069 / 500000000) (1292393071 / 500000000) (Real.log (828778306999 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (828778306999 / 62500000000) = -Real.log (62500000000 / 828778306999) := by
    rw [show ((828778306999 / 62500000000) : ℝ) = ((62500000000 / 828778306999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2600558263 / 1000000000) ≤ -Real.log (250000000000 / 3367814116711) ∧
    -Real.log (250000000000 / 3367814116711) ≤ (2600558267 / 1000000000) := by
  have h := checkLog_sound (w := (1367814116711 / 5367814116711)) (n := 12)
    (lo := (521116723 / 1000000000)) (hi := (130279181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3367814116711 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3367814116711 / 2000000000000) = 1/(250000000000 / 3367814116711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2600558263 / 1000000000) (2600558267 / 1000000000) (Real.log (3367814116711 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3367814116711 / 250000000000) = -Real.log (250000000000 / 3367814116711) := by
    rw [show ((3367814116711 / 250000000000) : ℝ) = ((250000000000 / 3367814116711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0198

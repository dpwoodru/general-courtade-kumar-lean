import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell164
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

theorem reflection_log_1_neg : (37205259 / 125000000) ≤ -Real.log (1024 / 1379) ∧
    -Real.log (1024 / 1379) ≤ (297642073 / 1000000000) := by
  have h := checkLog_sound (w := (355 / 2403)) (n := 12)
    (lo := (37205259 / 125000000)) (hi := (297642073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1379 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1379 / 1024) = 1/(1024 / 1379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (37205259 / 125000000) (297642073 / 1000000000) (Real.log (1379 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1379 / 1024) = -Real.log (1024 / 1379) := by
    rw [show ((1379 / 1024) : ℝ) = ((1024 / 1379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (85137549 / 200000000) ≤ -Real.log (669 / 1024) ∧
    -Real.log (669 / 1024) ≤ (212843873 / 500000000) := by
  have h := checkLog_sound (w := (355 / 1693)) (n := 12)
    (lo := (85137549 / 200000000)) (hi := (212843873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 669) = 1/(669 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-212843873 / 500000000) (-85137549 / 200000000) (Real.log (669 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (297206879 / 1000000000) ≤ -Real.log (1280 / 1723) ∧
    -Real.log (1280 / 1723) ≤ (1857543 / 6250000) := by
  have h := checkLog_sound (w := (443 / 3003)) (n := 12)
    (lo := (297206879 / 1000000000)) (hi := (1857543 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1723 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1723 / 1280) = 1/(1280 / 1723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (297206879 / 1000000000) (1857543 / 6250000) (Real.log (1723 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1723 / 1280) = -Real.log (1280 / 1723) := by
    rw [show ((1723 / 1280) : ℝ) = ((1280 / 1723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (212395643 / 500000000) ≤ -Real.log (837 / 1280) ∧
    -Real.log (837 / 1280) ≤ (424791287 / 1000000000) := by
  have h := checkLog_sound (w := (443 / 2117)) (n := 12)
    (lo := (212395643 / 500000000)) (hi := (424791287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 837) = 1/(837 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-424791287 / 1000000000) (-212395643 / 500000000) (Real.log (837 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (13746703 / 62500000) ≤ -Real.log (1000000 / 1246011) ∧
    -Real.log (1000000 / 1246011) ≤ (219947249 / 1000000000) := by
  have h := checkLog_sound (w := (246011 / 2246011)) (n := 12)
    (lo := (13746703 / 62500000)) (hi := (219947249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246011 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246011 / 1000000) = 1/(1000000 / 1246011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (13746703 / 62500000) (219947249 / 1000000000) (Real.log (1246011 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1246011 / 1000000) = -Real.log (1000000 / 1246011) := by
    rw [show ((1246011 / 1000000) : ℝ) = ((1000000 / 1246011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (282377499 / 1000000000) ≤ -Real.log (753989 / 1000000) ∧
    -Real.log (753989 / 1000000) ≤ (112951 / 400000) := by
  have h := checkLog_sound (w := (246011 / 1753989)) (n := 12)
    (lo := (282377499 / 1000000000)) (hi := (112951 / 400000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753989) = 1/(753989 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-112951 / 400000) (-282377499 / 1000000000) (Real.log (753989 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13767867 / 62500000) ≤ -Real.log (1000000 / 1246433) ∧
    -Real.log (1000000 / 1246433) ≤ (220285873 / 1000000000) := by
  have h := checkLog_sound (w := (246433 / 2246433)) (n := 12)
    (lo := (13767867 / 62500000)) (hi := (220285873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246433 / 1000000) = 1/(1000000 / 1246433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13767867 / 62500000) (220285873 / 1000000000) (Real.log (1246433 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1246433 / 1000000) = -Real.log (1000000 / 1246433) := by
    rw [show ((1246433 / 1000000) : ℝ) = ((1000000 / 1246433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (141468673 / 500000000) ≤ -Real.log (753567 / 1000000) ∧
    -Real.log (753567 / 1000000) ≤ (282937347 / 1000000000) := by
  have h := checkLog_sound (w := (246433 / 1753567)) (n := 12)
    (lo := (141468673 / 500000000)) (hi := (282937347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753567) = 1/(753567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-282937347 / 1000000000) (-141468673 / 500000000) (Real.log (753567 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32580511 / 200000000) ≤ -Real.log (500000 / 588461) ∧
    -Real.log (500000 / 588461) ≤ (40725639 / 250000000) := by
  have h := checkLog_sound (w := (88461 / 1088461)) (n := 12)
    (lo := (32580511 / 200000000)) (hi := (40725639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588461 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588461 / 500000) = 1/(500000 / 588461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32580511 / 200000000) (40725639 / 250000000) (Real.log (588461 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (588461 / 500000) = -Real.log (500000 / 588461) := by
    rw [show ((588461 / 500000) : ℝ) = ((500000 / 588461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (194704307 / 1000000000) ≤ -Real.log (411539 / 500000) ∧
    -Real.log (411539 / 500000) ≤ (48676077 / 250000000) := by
  have h := checkLog_sound (w := (88461 / 911539)) (n := 12)
    (lo := (194704307 / 1000000000)) (hi := (48676077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 411539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 411539) = 1/(411539 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-48676077 / 250000000) (-194704307 / 1000000000) (Real.log (411539 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (163169317 / 1000000000) ≤ -Real.log (250000 / 294309) ∧
    -Real.log (250000 / 294309) ≤ (81584659 / 500000000) := by
  have h := checkLog_sound (w := (44309 / 544309)) (n := 12)
    (lo := (163169317 / 1000000000)) (hi := (81584659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294309 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294309 / 250000) = 1/(250000 / 294309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (163169317 / 1000000000) (81584659 / 500000000) (Real.log (294309 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (294309 / 250000) = -Real.log (250000 / 294309) := by
    rw [show ((294309 / 250000) : ℝ) = ((250000 / 294309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1560687 / 8000000) ≤ -Real.log (205691 / 250000) ∧
    -Real.log (205691 / 250000) ≤ (48771469 / 250000000) := by
  have h := checkLog_sound (w := (44309 / 455691)) (n := 12)
    (lo := (1560687 / 8000000)) (hi := (48771469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 205691) = 1/(205691 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48771469 / 250000000) (-1560687 / 8000000) (Real.log (205691 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (144399633 / 200000000) ≤ -Real.log (50000000000 / 102927120669) ∧
    -Real.log (50000000000 / 102927120669) ≤ (721998167 / 1000000000) := by
  have h := checkLog_sound (w := (2927120669 / 202927120669)) (n := 12)
    (lo := (5770197 / 200000000)) (hi := (14425493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102927120669 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102927120669 / 100000000000) = 1/(50000000000 / 102927120669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (144399633 / 200000000) (721998167 / 1000000000) (Real.log (102927120669 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (102927120669 / 50000000000) = -Real.log (50000000000 / 102927120669) := by
    rw [show ((102927120669 / 50000000000) : ℝ) = ((50000000000 / 102927120669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (723329817 / 1000000000) ≤ -Real.log (250000000000 / 515321375187) ∧
    -Real.log (250000000000 / 515321375187) ≤ (723329819 / 1000000000) := by
  have h := checkLog_sound (w := (15321375187 / 1015321375187)) (n := 12)
    (lo := (30182637 / 1000000000)) (hi := (15091319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((515321375187 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(515321375187 / 500000000000) = 1/(250000000000 / 515321375187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (723329817 / 1000000000) (723329819 / 1000000000) (Real.log (515321375187 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (515321375187 / 250000000000) = -Real.log (250000000000 / 515321375187) := by
    rw [show ((515321375187 / 250000000000) : ℝ) = ((250000000000 / 515321375187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (125581187 / 250000000) ≤ -Real.log (500000000000 / 826279295851) ∧
    -Real.log (500000000000 / 826279295851) ≤ (502324749 / 1000000000) := by
  have h := checkLog_sound (w := (326279295851 / 1326279295851)) (n := 12)
    (lo := (125581187 / 250000000)) (hi := (502324749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826279295851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826279295851 / 500000000000) = 1/(500000000000 / 826279295851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (125581187 / 250000000) (502324749 / 1000000000) (Real.log (826279295851 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (826279295851 / 500000000000) = -Real.log (500000000000 / 826279295851) := by
    rw [show ((826279295851 / 500000000000) : ℝ) = ((500000000000 / 826279295851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (251611609 / 500000000) ≤ -Real.log (500000000000 / 827022016623) ∧
    -Real.log (500000000000 / 827022016623) ≤ (503223219 / 1000000000) := by
  have h := checkLog_sound (w := (327022016623 / 1327022016623)) (n := 12)
    (lo := (251611609 / 500000000)) (hi := (503223219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827022016623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827022016623 / 500000000000) = 1/(500000000000 / 827022016623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (251611609 / 500000000) (503223219 / 1000000000) (Real.log (827022016623 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (827022016623 / 500000000000) = -Real.log (500000000000 / 827022016623) := by
    rw [show ((827022016623 / 500000000000) : ℝ) = ((500000000000 / 827022016623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (357606863 / 1000000000) ≤ -Real.log (500000000000 / 714951681371) ∧
    -Real.log (500000000000 / 714951681371) ≤ (22350429 / 62500000) := by
  have h := checkLog_sound (w := (214951681371 / 1214951681371)) (n := 12)
    (lo := (357606863 / 1000000000)) (hi := (22350429 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714951681371 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714951681371 / 500000000000) = 1/(500000000000 / 714951681371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (357606863 / 1000000000) (22350429 / 62500000) (Real.log (714951681371 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (714951681371 / 500000000000) = -Real.log (500000000000 / 714951681371) := by
    rw [show ((714951681371 / 500000000000) : ℝ) = ((500000000000 / 714951681371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (358255193 / 1000000000) ≤ -Real.log (125000000000 / 178853839011) ∧
    -Real.log (125000000000 / 178853839011) ≤ (179127597 / 500000000) := by
  have h := checkLog_sound (w := (53853839011 / 303853839011)) (n := 12)
    (lo := (358255193 / 1000000000)) (hi := (179127597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178853839011 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178853839011 / 125000000000) = 1/(125000000000 / 178853839011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (358255193 / 1000000000) (179127597 / 500000000) (Real.log (178853839011 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (178853839011 / 125000000000) = -Real.log (125000000000 / 178853839011) := by
    rw [show ((178853839011 / 125000000000) : ℝ) = ((125000000000 / 178853839011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (31916557 / 1000000000) ≤ -Real.log (60536712519 / 62500000000) ∧
    -Real.log (60536712519 / 62500000000) ≤ (15958279 / 500000000) := by
  have h := checkLog_sound (w := (1963287481 / 123036712519)) (n := 12)
    (lo := (31916557 / 1000000000)) (hi := (15958279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60536712519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60536712519) = 1/(60536712519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-15958279 / 500000000) (-31916557 / 1000000000) (Real.log (60536712519 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (31801751 / 1000000000) ≤ -Real.log (242174651479 / 250000000000) ∧
    -Real.log (242174651479 / 250000000000) ≤ (3975219 / 125000000) := by
  have h := checkLog_sound (w := (7825348521 / 492174651479)) (n := 12)
    (lo := (31801751 / 1000000000)) (hi := (3975219 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242174651479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242174651479) = 1/(242174651479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3975219 / 125000000) (-31801751 / 1000000000) (Real.log (242174651479 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell164

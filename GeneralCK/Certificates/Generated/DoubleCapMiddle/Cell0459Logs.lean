import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0459
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

theorem reflection_log_1_neg : (11623561 / 62500000) ≤ -Real.log (10240 / 12333) ∧
    -Real.log (10240 / 12333) ≤ (185976977 / 1000000000) := by
  have h := checkLog_sound (w := (2093 / 22573)) (n := 12)
    (lo := (11623561 / 62500000)) (hi := (185976977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12333 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12333 / 10240) = 1/(10240 / 12333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11623561 / 62500000) (185976977 / 1000000000) (Real.log (12333 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12333 / 10240) = -Real.log (10240 / 12333) := by
    rw [show ((12333 / 10240) : ℝ) = ((10240 / 12333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (114325929 / 500000000) ≤ -Real.log (8147 / 10240) ∧
    -Real.log (8147 / 10240) ≤ (228651859 / 1000000000) := by
  have h := checkLog_sound (w := (2093 / 18387)) (n := 12)
    (lo := (114325929 / 500000000)) (hi := (228651859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8147) = 1/(8147 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-228651859 / 1000000000) (-114325929 / 500000000) (Real.log (8147 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (185733697 / 1000000000) ≤ -Real.log (1024 / 1233) ∧
    -Real.log (1024 / 1233) ≤ (92866849 / 500000000) := by
  have h := checkLog_sound (w := (209 / 2257)) (n := 12)
    (lo := (185733697 / 1000000000)) (hi := (92866849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233 / 1024) = 1/(1024 / 1233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (185733697 / 1000000000) (92866849 / 500000000) (Real.log (1233 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1233 / 1024) = -Real.log (1024 / 1233) := by
    rw [show ((1233 / 1024) : ℝ) = ((1024 / 1233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57070923 / 250000000) ≤ -Real.log (815 / 1024) ∧
    -Real.log (815 / 1024) ≤ (228283693 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1839)) (n := 12)
    (lo := (57070923 / 250000000)) (hi := (228283693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 815) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 815) = 1/(815 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-228283693 / 1000000000) (-57070923 / 250000000) (Real.log (815 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (171365257 / 500000000) ≤ -Real.log (5120 / 7213) ∧
    -Real.log (5120 / 7213) ≤ (68546103 / 200000000) := by
  have h := checkLog_sound (w := (2093 / 12333)) (n := 12)
    (lo := (171365257 / 500000000)) (hi := (68546103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7213 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7213 / 5120) = 1/(5120 / 7213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (171365257 / 500000000) (68546103 / 200000000) (Real.log (7213 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7213 / 5120) = -Real.log (5120 / 7213) := by
    rw [show ((7213 / 5120) : ℝ) = ((5120 / 7213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (525582409 / 1000000000) ≤ -Real.log (3027 / 5120) ∧
    -Real.log (3027 / 5120) ≤ (52558241 / 100000000) := by
  have h := checkLog_sound (w := (2093 / 8147)) (n := 12)
    (lo := (525582409 / 1000000000)) (hi := (52558241 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3027) = 1/(3027 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-52558241 / 100000000) (-525582409 / 1000000000) (Real.log (3027 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (21394657 / 62500000) ≤ -Real.log (512 / 721) ∧
    -Real.log (512 / 721) ≤ (342314513 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1233)) (n := 12)
    (lo := (21394657 / 62500000)) (hi := (342314513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721 / 512) = 1/(512 / 721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (21394657 / 62500000) (342314513 / 1000000000) (Real.log (721 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (721 / 512) = -Real.log (512 / 721) := by
    rw [show ((721 / 512) : ℝ) = ((512 / 721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (524591819 / 1000000000) ≤ -Real.log (303 / 512) ∧
    -Real.log (303 / 512) ≤ (26229591 / 50000000) := by
  have h := checkLog_sound (w := (209 / 815)) (n := 12)
    (lo := (524591819 / 1000000000)) (hi := (26229591 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 303) = 1/(303 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26229591 / 50000000) (-524591819 / 1000000000) (Real.log (303 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (127630703 / 500000000) ≤ -Real.log (1000000 / 1290799) ∧
    -Real.log (1000000 / 1290799) ≤ (255261407 / 1000000000) := by
  have h := checkLog_sound (w := (290799 / 2290799)) (n := 12)
    (lo := (127630703 / 500000000)) (hi := (255261407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1290799 / 1000000) = 1/(1000000 / 1290799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (127630703 / 500000000) (255261407 / 1000000000) (Real.log (1290799 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1290799 / 1000000) = -Real.log (1000000 / 1290799) := by
    rw [show ((1290799 / 1000000) : ℝ) = ((1000000 / 1290799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (171808147 / 500000000) ≤ -Real.log (709201 / 1000000) ∧
    -Real.log (709201 / 1000000) ≤ (68723259 / 200000000) := by
  have h := checkLog_sound (w := (290799 / 1709201)) (n := 12)
    (lo := (171808147 / 500000000)) (hi := (68723259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 709201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 709201) = 1/(709201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-68723259 / 200000000) (-171808147 / 500000000) (Real.log (709201 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (51118121 / 200000000) ≤ -Real.log (125000 / 161403) ∧
    -Real.log (125000 / 161403) ≤ (127795303 / 500000000) := by
  have h := checkLog_sound (w := (36403 / 286403)) (n := 12)
    (lo := (51118121 / 200000000)) (hi := (127795303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161403 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161403 / 125000) = 1/(125000 / 161403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (51118121 / 200000000) (127795303 / 500000000) (Real.log (161403 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (161403 / 125000) = -Real.log (125000 / 161403) := by
    rw [show ((161403 / 125000) : ℝ) = ((125000 / 161403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (17210787 / 50000000) ≤ -Real.log (88597 / 125000) ∧
    -Real.log (88597 / 125000) ≤ (344215741 / 1000000000) := by
  have h := checkLog_sound (w := (36403 / 213597)) (n := 12)
    (lo := (17210787 / 50000000)) (hi := (344215741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88597) = 1/(88597 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-344215741 / 1000000000) (-17210787 / 50000000) (Real.log (88597 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (95539879 / 500000000) ≤ -Real.log (250000 / 302639) ∧
    -Real.log (250000 / 302639) ≤ (191079759 / 1000000000) := by
  have h := checkLog_sound (w := (52639 / 552639)) (n := 12)
    (lo := (95539879 / 500000000)) (hi := (191079759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302639 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302639 / 250000) = 1/(250000 / 302639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (95539879 / 500000000) (191079759 / 1000000000) (Real.log (302639 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (302639 / 250000) = -Real.log (250000 / 302639) := by
    rw [show ((302639 / 250000) : ℝ) = ((250000 / 302639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (118213189 / 500000000) ≤ -Real.log (197361 / 250000) ∧
    -Real.log (197361 / 250000) ≤ (236426379 / 1000000000) := by
  have h := checkLog_sound (w := (52639 / 447361)) (n := 12)
    (lo := (118213189 / 500000000)) (hi := (236426379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197361) = 1/(197361 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-236426379 / 1000000000) (-118213189 / 500000000) (Real.log (197361 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (95673271 / 500000000) ≤ -Real.log (1000000 / 1210879) ∧
    -Real.log (1000000 / 1210879) ≤ (191346543 / 1000000000) := by
  have h := checkLog_sound (w := (210879 / 2210879)) (n := 12)
    (lo := (95673271 / 500000000)) (hi := (191346543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210879 / 1000000) = 1/(1000000 / 1210879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (95673271 / 500000000) (191346543 / 1000000000) (Real.log (1210879 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1210879 / 1000000) = -Real.log (1000000 / 1210879) := by
    rw [show ((1210879 / 1000000) : ℝ) = ((1000000 / 1210879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (236835611 / 1000000000) ≤ -Real.log (789121 / 1000000) ∧
    -Real.log (789121 / 1000000) ≤ (59208903 / 250000000) := by
  have h := checkLog_sound (w := (210879 / 1789121)) (n := 12)
    (lo := (236835611 / 1000000000)) (hi := (59208903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789121) = 1/(789121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-59208903 / 250000000) (-236835611 / 1000000000) (Real.log (789121 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (598877701 / 1000000000) ≤ -Real.log (15625000000 / 28438671653) ∧
    -Real.log (15625000000 / 28438671653) ≤ (299438851 / 500000000) := by
  have h := checkLog_sound (w := (12813671653 / 44063671653)) (n := 12)
    (lo := (598877701 / 1000000000)) (hi := (299438851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28438671653 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28438671653 / 15625000000) = 1/(15625000000 / 28438671653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (598877701 / 1000000000) (299438851 / 500000000) (Real.log (28438671653 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (28438671653 / 15625000000) = -Real.log (15625000000 / 28438671653) := by
    rw [show ((28438671653 / 15625000000) : ℝ) = ((15625000000 / 28438671653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (299903173 / 500000000) ≤ -Real.log (500000000000 / 910882987009) ∧
    -Real.log (500000000000 / 910882987009) ≤ (599806347 / 1000000000) := by
  have h := checkLog_sound (w := (410882987009 / 1410882987009)) (n := 12)
    (lo := (299903173 / 500000000)) (hi := (599806347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((910882987009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(910882987009 / 500000000000) = 1/(500000000000 / 910882987009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (299903173 / 500000000) (599806347 / 1000000000) (Real.log (910882987009 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (910882987009 / 500000000000) = -Real.log (500000000000 / 910882987009) := by
    rw [show ((910882987009 / 500000000000) : ℝ) = ((500000000000 / 910882987009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (53438267 / 125000000) ≤ -Real.log (125000000000 / 191678573781) ∧
    -Real.log (125000000000 / 191678573781) ≤ (427506137 / 1000000000) := by
  have h := checkLog_sound (w := (66678573781 / 316678573781)) (n := 12)
    (lo := (53438267 / 125000000)) (hi := (427506137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191678573781 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191678573781 / 125000000000) = 1/(125000000000 / 191678573781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (53438267 / 125000000) (427506137 / 1000000000) (Real.log (191678573781 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (191678573781 / 125000000000) = -Real.log (125000000000 / 191678573781) := by
    rw [show ((191678573781 / 125000000000) : ℝ) = ((125000000000 / 191678573781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (428182153 / 1000000000) ≤ -Real.log (15625000000 / 23976024431) ∧
    -Real.log (15625000000 / 23976024431) ≤ (214091077 / 500000000) := by
  have h := checkLog_sound (w := (8351024431 / 39601024431)) (n := 12)
    (lo := (428182153 / 1000000000)) (hi := (214091077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23976024431 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23976024431 / 15625000000) = 1/(15625000000 / 23976024431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (428182153 / 1000000000) (214091077 / 500000000) (Real.log (23976024431 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (23976024431 / 15625000000) = -Real.log (15625000000 / 23976024431) := by
    rw [show ((23976024431 / 15625000000) : ℝ) = ((15625000000 / 23976024431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0459

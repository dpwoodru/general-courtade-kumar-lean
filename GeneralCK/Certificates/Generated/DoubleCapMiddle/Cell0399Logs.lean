import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0399
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

theorem reflection_log_1_neg : (50116621 / 250000000) ≤ -Real.log (10240 / 12513) ∧
    -Real.log (10240 / 12513) ≤ (40093297 / 200000000) := by
  have h := checkLog_sound (w := (2273 / 22753)) (n := 12)
    (lo := (50116621 / 250000000)) (hi := (40093297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12513 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12513 / 10240) = 1/(10240 / 12513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50116621 / 250000000) (40093297 / 200000000) (Real.log (12513 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12513 / 10240) = -Real.log (10240 / 12513) := by
    rw [show ((12513 / 10240) : ℝ) = ((10240 / 12513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (250993609 / 1000000000) ≤ -Real.log (7967 / 10240) ∧
    -Real.log (7967 / 10240) ≤ (25099361 / 100000000) := by
  have h := checkLog_sound (w := (2273 / 18207)) (n := 12)
    (lo := (250993609 / 1000000000)) (hi := (25099361 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7967) = 1/(7967 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-25099361 / 100000000) (-250993609 / 1000000000) (Real.log (7967 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12514169 / 62500000) ≤ -Real.log (1024 / 1251) ∧
    -Real.log (1024 / 1251) ≤ (40045341 / 200000000) := by
  have h := checkLog_sound (w := (227 / 2275)) (n := 12)
    (lo := (12514169 / 62500000)) (hi := (40045341 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251 / 1024) = 1/(1024 / 1251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12514169 / 62500000) (40045341 / 200000000) (Real.log (1251 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1251 / 1024) = -Real.log (1024 / 1251) := by
    rw [show ((1251 / 1024) : ℝ) = ((1024 / 1251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (125308563 / 500000000) ≤ -Real.log (797 / 1024) ∧
    -Real.log (797 / 1024) ≤ (250617127 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 1821)) (n := 12)
    (lo := (125308563 / 500000000)) (hi := (250617127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 797) = 1/(797 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-250617127 / 1000000000) (-125308563 / 500000000) (Real.log (797 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (367379167 / 1000000000) ≤ -Real.log (5120 / 7393) ∧
    -Real.log (5120 / 7393) ≤ (11480599 / 31250000) := by
  have h := checkLog_sound (w := (2273 / 12513)) (n := 12)
    (lo := (367379167 / 1000000000)) (hi := (11480599 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7393 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7393 / 5120) = 1/(5120 / 7393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (367379167 / 1000000000) (11480599 / 31250000) (Real.log (7393 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7393 / 5120) = -Real.log (5120 / 7393) := by
    rw [show ((7393 / 5120) : ℝ) = ((5120 / 7393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (58688863 / 100000000) ≤ -Real.log (2847 / 5120) ∧
    -Real.log (2847 / 5120) ≤ (586888631 / 1000000000) := by
  have h := checkLog_sound (w := (2273 / 7967)) (n := 12)
    (lo := (58688863 / 100000000)) (hi := (586888631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2847) = 1/(2847 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-586888631 / 1000000000) (-58688863 / 100000000) (Real.log (2847 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (73394659 / 200000000) ≤ -Real.log (512 / 739) ∧
    -Real.log (512 / 739) ≤ (22935831 / 62500000) := by
  have h := checkLog_sound (w := (227 / 1251)) (n := 12)
    (lo := (73394659 / 200000000)) (hi := (22935831 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739 / 512) = 1/(512 / 739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (73394659 / 200000000) (22935831 / 62500000) (Real.log (739 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (739 / 512) = -Real.log (512 / 739) := by
    rw [show ((739 / 512) : ℝ) = ((512 / 739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (146458861 / 250000000) ≤ -Real.log (285 / 512) ∧
    -Real.log (285 / 512) ≤ (117167089 / 200000000) := by
  have h := checkLog_sound (w := (227 / 797)) (n := 12)
    (lo := (146458861 / 250000000)) (hi := (117167089 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 285) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 285) = 1/(285 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-117167089 / 200000000) (-146458861 / 250000000) (Real.log (285 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (274827809 / 1000000000) ≤ -Real.log (62500 / 82269) ∧
    -Real.log (62500 / 82269) ≤ (27482781 / 100000000) := by
  have h := checkLog_sound (w := (19769 / 144769)) (n := 12)
    (lo := (274827809 / 1000000000)) (hi := (27482781 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82269 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82269 / 62500) = 1/(62500 / 82269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (274827809 / 1000000000) (27482781 / 100000000) (Real.log (82269 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (82269 / 62500) = -Real.log (62500 / 82269) := by
    rw [show ((82269 / 62500) : ℝ) = ((62500 / 82269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (23765119 / 62500000) ≤ -Real.log (42731 / 62500) ∧
    -Real.log (42731 / 62500) ≤ (76048381 / 200000000) := by
  have h := checkLog_sound (w := (19769 / 105231)) (n := 12)
    (lo := (23765119 / 62500000)) (hi := (76048381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42731) = 1/(42731 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-76048381 / 200000000) (-23765119 / 62500000) (Real.log (42731 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (275152149 / 1000000000) ≤ -Real.log (1000000 / 1316731) ∧
    -Real.log (1000000 / 1316731) ≤ (5503043 / 20000000) := by
  have h := checkLog_sound (w := (316731 / 2316731)) (n := 12)
    (lo := (275152149 / 1000000000)) (hi := (5503043 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1316731 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1316731 / 1000000) = 1/(1000000 / 1316731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (275152149 / 1000000000) (5503043 / 20000000) (Real.log (1316731 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1316731 / 1000000) = -Real.log (1000000 / 1316731) := by
    rw [show ((1316731 / 1000000) : ℝ) = ((1000000 / 1316731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (190433323 / 500000000) ≤ -Real.log (683269 / 1000000) ∧
    -Real.log (683269 / 1000000) ≤ (380866647 / 1000000000) := by
  have h := checkLog_sound (w := (316731 / 1683269)) (n := 12)
    (lo := (190433323 / 500000000)) (hi := (380866647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 683269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 683269) = 1/(683269 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-380866647 / 1000000000) (-190433323 / 500000000) (Real.log (683269 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51759843 / 250000000) ≤ -Real.log (1000000 / 1230031) ∧
    -Real.log (1000000 / 1230031) ≤ (207039373 / 1000000000) := by
  have h := checkLog_sound (w := (230031 / 2230031)) (n := 12)
    (lo := (51759843 / 250000000)) (hi := (207039373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230031 / 1000000) = 1/(1000000 / 1230031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51759843 / 250000000) (207039373 / 1000000000) (Real.log (1230031 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1230031 / 1000000) = -Real.log (1000000 / 1230031) := by
    rw [show ((1230031 / 1000000) : ℝ) = ((1000000 / 1230031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (8168907 / 31250000) ≤ -Real.log (769969 / 1000000) ∧
    -Real.log (769969 / 1000000) ≤ (10456201 / 40000000) := by
  have h := checkLog_sound (w := (230031 / 1769969)) (n := 12)
    (lo := (8168907 / 31250000)) (hi := (10456201 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769969) = 1/(769969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10456201 / 40000000) (-8168907 / 31250000) (Real.log (769969 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (207306809 / 1000000000) ≤ -Real.log (25000 / 30759) ∧
    -Real.log (25000 / 30759) ≤ (20730681 / 100000000) := by
  have h := checkLog_sound (w := (5759 / 55759)) (n := 12)
    (lo := (207306809 / 1000000000)) (hi := (20730681 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30759 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30759 / 25000) = 1/(25000 / 30759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (207306809 / 1000000000) (20730681 / 100000000) (Real.log (30759 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (30759 / 25000) = -Real.log (25000 / 30759) := by
    rw [show ((30759 / 25000) : ℝ) = ((25000 / 30759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (52366481 / 200000000) ≤ -Real.log (19241 / 25000) ∧
    -Real.log (19241 / 25000) ≤ (130916203 / 500000000) := by
  have h := checkLog_sound (w := (5759 / 44241)) (n := 12)
    (lo := (52366481 / 200000000)) (hi := (130916203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19241) = 1/(19241 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-130916203 / 500000000) (-52366481 / 200000000) (Real.log (19241 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (655069713 / 1000000000) ≤ -Real.log (500000000000 / 962638365589) ∧
    -Real.log (500000000000 / 962638365589) ≤ (327534857 / 500000000) := by
  have h := checkLog_sound (w := (462638365589 / 1462638365589)) (n := 12)
    (lo := (655069713 / 1000000000)) (hi := (327534857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((962638365589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(962638365589 / 500000000000) = 1/(500000000000 / 962638365589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (655069713 / 1000000000) (327534857 / 500000000) (Real.log (962638365589 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (962638365589 / 500000000000) = -Real.log (500000000000 / 962638365589) := by
    rw [show ((962638365589 / 500000000000) : ℝ) = ((500000000000 / 962638365589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (164004699 / 250000000) ≤ -Real.log (500000000000 / 963552422253) ∧
    -Real.log (500000000000 / 963552422253) ≤ (656018797 / 1000000000) := by
  have h := checkLog_sound (w := (463552422253 / 1463552422253)) (n := 12)
    (lo := (164004699 / 250000000)) (hi := (656018797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963552422253 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(963552422253 / 500000000000) = 1/(500000000000 / 963552422253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (164004699 / 250000000) (656018797 / 1000000000) (Real.log (963552422253 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (963552422253 / 500000000000) = -Real.log (500000000000 / 963552422253) := by
    rw [show ((963552422253 / 500000000000) : ℝ) = ((500000000000 / 963552422253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (468444397 / 1000000000) ≤ -Real.log (500000000000 / 798753586183) ∧
    -Real.log (500000000000 / 798753586183) ≤ (234222199 / 500000000) := by
  have h := checkLog_sound (w := (298753586183 / 1298753586183)) (n := 12)
    (lo := (468444397 / 1000000000)) (hi := (234222199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798753586183 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798753586183 / 500000000000) = 1/(500000000000 / 798753586183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (468444397 / 1000000000) (234222199 / 500000000) (Real.log (798753586183 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (798753586183 / 500000000000) = -Real.log (500000000000 / 798753586183) := by
    rw [show ((798753586183 / 500000000000) : ℝ) = ((500000000000 / 798753586183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (93827843 / 200000000) ≤ -Real.log (62500000000 / 99913595967) ∧
    -Real.log (62500000000 / 99913595967) ≤ (29321201 / 62500000) := by
  have h := checkLog_sound (w := (37413595967 / 162413595967)) (n := 12)
    (lo := (93827843 / 200000000)) (hi := (29321201 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99913595967 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99913595967 / 62500000000) = 1/(62500000000 / 99913595967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (93827843 / 200000000) (29321201 / 62500000) (Real.log (99913595967 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (99913595967 / 62500000000) = -Real.log (62500000000 / 99913595967) := by
    rw [show ((99913595967 / 62500000000) : ℝ) = ((62500000000 / 99913595967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0399

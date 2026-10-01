import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0318
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

theorem reflection_log_1_neg : (219700129 / 1000000000) ≤ -Real.log (2560 / 3189) ∧
    -Real.log (2560 / 3189) ≤ (21970013 / 100000000) := by
  have h := checkLog_sound (w := (629 / 5749)) (n := 12)
    (lo := (219700129 / 1000000000)) (hi := (21970013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3189 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3189 / 2560) = 1/(2560 / 3189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (219700129 / 1000000000) (21970013 / 100000000) (Real.log (3189 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3189 / 2560) = -Real.log (2560 / 3189) := by
    rw [show ((3189 / 2560) : ℝ) = ((2560 / 3189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (56393851 / 200000000) ≤ -Real.log (1931 / 2560) ∧
    -Real.log (1931 / 2560) ≤ (35246157 / 125000000) := by
  have h := checkLog_sound (w := (629 / 4491)) (n := 12)
    (lo := (56393851 / 200000000)) (hi := (35246157 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1931) = 1/(1931 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-35246157 / 125000000) (-56393851 / 200000000) (Real.log (1931 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (109732459 / 500000000) ≤ -Real.log (10240 / 12753) ∧
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


theorem reflection_log_3 : Bounds (109732459 / 500000000) (219464919 / 1000000000) (Real.log (12753 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12753 / 10240) = -Real.log (10240 / 12753) := by
    rw [show ((12753 / 10240) : ℝ) = ((10240 / 12753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (28158093 / 100000000) ≤ -Real.log (7727 / 10240) ∧
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


theorem reflection_log_4 : Bounds (-281580931 / 1000000000) (-28158093 / 100000000) (Real.log (7727 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (199859733 / 500000000) ≤ -Real.log (1280 / 1909) ∧
    -Real.log (1280 / 1909) ≤ (399719467 / 1000000000) := by
  have h := checkLog_sound (w := (629 / 3189)) (n := 12)
    (lo := (199859733 / 500000000)) (hi := (399719467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1909 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1909 / 1280) = 1/(1280 / 1909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (199859733 / 500000000) (399719467 / 1000000000) (Real.log (1909 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1909 / 1280) = -Real.log (1280 / 1909) := by
    rw [show ((1909 / 1280) : ℝ) = ((1280 / 1909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (338052857 / 500000000) ≤ -Real.log (651 / 1280) ∧
    -Real.log (651 / 1280) ≤ (135221143 / 200000000) := by
  have h := checkLog_sound (w := (629 / 1931)) (n := 12)
    (lo := (338052857 / 500000000)) (hi := (135221143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 651) = 1/(651 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-135221143 / 200000000) (-338052857 / 500000000) (Real.log (651 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (399326513 / 1000000000) ≤ -Real.log (5120 / 7633) ∧
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


theorem reflection_log_7 : Bounds (399326513 / 1000000000) (199663257 / 500000000) (Real.log (7633 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7633 / 5120) = -Real.log (5120 / 7633) := by
    rw [show ((7633 / 5120) : ℝ) = ((5120 / 7633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10546161 / 15625000) ≤ -Real.log (2607 / 5120) ∧
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


theorem reflection_log_8 : Bounds (-134990861 / 200000000) (-10546161 / 15625000) (Real.log (2607 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75201457 / 250000000) ≤ -Real.log (1000000 / 1350947) ∧
    -Real.log (1000000 / 1350947) ≤ (300805829 / 1000000000) := by
  have h := checkLog_sound (w := (350947 / 2350947)) (n := 12)
    (lo := (75201457 / 250000000)) (hi := (300805829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1350947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1350947 / 1000000) = 1/(1000000 / 1350947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75201457 / 250000000) (300805829 / 1000000000) (Real.log (1350947 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1350947 / 1000000) = -Real.log (1000000 / 1350947) := by
    rw [show ((1350947 / 1000000) : ℝ) = ((1000000 / 1350947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (432240901 / 1000000000) ≤ -Real.log (649053 / 1000000) ∧
    -Real.log (649053 / 1000000) ≤ (216120451 / 500000000) := by
  have h := checkLog_sound (w := (350947 / 1649053)) (n := 12)
    (lo := (432240901 / 1000000000)) (hi := (216120451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 649053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 649053) = 1/(649053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-216120451 / 500000000) (-432240901 / 1000000000) (Real.log (649053 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37640509 / 125000000) ≤ -Real.log (1000000 / 1351377) ∧
    -Real.log (1000000 / 1351377) ≤ (301124073 / 1000000000) := by
  have h := checkLog_sound (w := (351377 / 2351377)) (n := 12)
    (lo := (37640509 / 125000000)) (hi := (301124073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351377 / 1000000) = 1/(1000000 / 1351377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37640509 / 125000000) (301124073 / 1000000000) (Real.log (1351377 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1351377 / 1000000) = -Real.log (1000000 / 1351377) := by
    rw [show ((1351377 / 1000000) : ℝ) = ((1000000 / 1351377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (54112953 / 125000000) ≤ -Real.log (648623 / 1000000) ∧
    -Real.log (648623 / 1000000) ≤ (3463229 / 8000000) := by
  have h := checkLog_sound (w := (351377 / 1648623)) (n := 12)
    (lo := (54112953 / 125000000)) (hi := (3463229 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 648623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 648623) = 1/(648623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3463229 / 8000000) (-54112953 / 125000000) (Real.log (648623 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (228657919 / 1000000000) ≤ -Real.log (62500 / 78557) ∧
    -Real.log (62500 / 78557) ≤ (178639 / 781250) := by
  have h := checkLog_sound (w := (16057 / 141057)) (n := 12)
    (lo := (228657919 / 1000000000)) (hi := (178639 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78557 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78557 / 62500) = 1/(62500 / 78557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (228657919 / 1000000000) (178639 / 781250) (Real.log (78557 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (78557 / 62500) = -Real.log (62500 / 78557) := by
    rw [show ((78557 / 62500) : ℝ) = ((62500 / 78557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (148470401 / 500000000) ≤ -Real.log (46443 / 62500) ∧
    -Real.log (46443 / 62500) ≤ (296940803 / 1000000000) := by
  have h := checkLog_sound (w := (16057 / 108943)) (n := 12)
    (lo := (148470401 / 500000000)) (hi := (296940803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46443) = 1/(46443 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-296940803 / 1000000000) (-148470401 / 500000000) (Real.log (46443 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (114463 / 500000) ≤ -Real.log (1000000 / 1257249) ∧
    -Real.log (1000000 / 1257249) ≤ (228926001 / 1000000000) := by
  have h := checkLog_sound (w := (257249 / 2257249)) (n := 12)
    (lo := (114463 / 500000)) (hi := (228926001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257249 / 1000000) = 1/(1000000 / 1257249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (114463 / 500000) (228926001 / 1000000000) (Real.log (1257249 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1257249 / 1000000) = -Real.log (1000000 / 1257249) := by
    rw [show ((1257249 / 1000000) : ℝ) = ((1000000 / 1257249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (148697209 / 500000000) ≤ -Real.log (742751 / 1000000) ∧
    -Real.log (742751 / 1000000) ≤ (297394419 / 1000000000) := by
  have h := checkLog_sound (w := (257249 / 1742751)) (n := 12)
    (lo := (148697209 / 500000000)) (hi := (297394419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742751) = 1/(742751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-297394419 / 1000000000) (-148697209 / 500000000) (Real.log (742751 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (91630841 / 125000000) ≤ -Real.log (500000000000 / 1040706228921) ∧
    -Real.log (500000000000 / 1040706228921) ≤ (73304673 / 100000000) := by
  have h := checkLog_sound (w := (40706228921 / 2040706228921)) (n := 12)
    (lo := (9974887 / 250000000)) (hi := (39899549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1040706228921 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1040706228921 / 1000000000000) = 1/(500000000000 / 1040706228921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (91630841 / 125000000) (73304673 / 100000000) (Real.log (1040706228921 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1040706228921 / 500000000000) = -Real.log (500000000000 / 1040706228921) := by
    rw [show ((1040706228921 / 500000000000) : ℝ) = ((500000000000 / 1040706228921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (45876731 / 62500000) ≤ -Real.log (500000000000 / 1041727629147) ∧
    -Real.log (500000000000 / 1041727629147) ≤ (367013849 / 500000000) := by
  have h := checkLog_sound (w := (41727629147 / 2041727629147)) (n := 12)
    (lo := (10220129 / 250000000)) (hi := (40880517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1041727629147 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1041727629147 / 1000000000000) = 1/(500000000000 / 1041727629147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (45876731 / 62500000) (367013849 / 500000000) (Real.log (1041727629147 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1041727629147 / 500000000000) = -Real.log (500000000000 / 1041727629147) := by
    rw [show ((1041727629147 / 500000000000) : ℝ) = ((500000000000 / 1041727629147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (525598721 / 1000000000) ≤ -Real.log (250000000000 / 422867816463) ∧
    -Real.log (250000000000 / 422867816463) ≤ (262799361 / 500000000) := by
  have h := checkLog_sound (w := (172867816463 / 672867816463)) (n := 12)
    (lo := (525598721 / 1000000000)) (hi := (262799361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422867816463 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422867816463 / 250000000000) = 1/(250000000000 / 422867816463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (525598721 / 1000000000) (262799361 / 500000000) (Real.log (422867816463 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (422867816463 / 250000000000) = -Real.log (250000000000 / 422867816463) := by
    rw [show ((422867816463 / 250000000000) : ℝ) = ((250000000000 / 422867816463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (263160209 / 500000000) ≤ -Real.log (125000000000 / 211586554579) ∧
    -Real.log (125000000000 / 211586554579) ≤ (526320419 / 1000000000) := by
  have h := checkLog_sound (w := (86586554579 / 336586554579)) (n := 12)
    (lo := (263160209 / 500000000)) (hi := (526320419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211586554579 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211586554579 / 125000000000) = 1/(125000000000 / 211586554579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (263160209 / 500000000) (526320419 / 1000000000) (Real.log (211586554579 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (211586554579 / 125000000000) = -Real.log (125000000000 / 211586554579) := by
    rw [show ((211586554579 / 125000000000) : ℝ) = ((125000000000 / 211586554579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0318

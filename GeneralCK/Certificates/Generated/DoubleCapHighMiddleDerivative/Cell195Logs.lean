import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell195
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

theorem reflection_log_1_neg : (311039953 / 1000000000) ≤ -Real.log (1280 / 1747) ∧
    -Real.log (1280 / 1747) ≤ (155519977 / 500000000) := by
  have h := checkLog_sound (w := (467 / 3027)) (n := 12)
    (lo := (311039953 / 1000000000)) (hi := (155519977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1747 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1747 / 1280) = 1/(1280 / 1747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (311039953 / 1000000000) (155519977 / 500000000) (Real.log (1747 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1747 / 1280) = -Real.log (1280 / 1747) := by
    rw [show ((1747 / 1280) : ℝ) = ((1280 / 1747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (453884247 / 1000000000) ≤ -Real.log (813 / 1280) ∧
    -Real.log (813 / 1280) ≤ (56735531 / 125000000) := by
  have h := checkLog_sound (w := (467 / 2093)) (n := 12)
    (lo := (453884247 / 1000000000)) (hi := (56735531 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 813) = 1/(813 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-56735531 / 125000000) (-453884247 / 1000000000) (Real.log (813 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (310610553 / 1000000000) ≤ -Real.log (1024 / 1397) ∧
    -Real.log (1024 / 1397) ≤ (155305277 / 500000000) := by
  have h := checkLog_sound (w := (373 / 2421)) (n := 12)
    (lo := (310610553 / 1000000000)) (hi := (155305277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397 / 1024) = 1/(1024 / 1397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (310610553 / 1000000000) (155305277 / 500000000) (Real.log (1397 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1397 / 1024) = -Real.log (1024 / 1397) := by
    rw [show ((1397 / 1024) : ℝ) = ((1024 / 1397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (452962163 / 1000000000) ≤ -Real.log (651 / 1024) ∧
    -Real.log (651 / 1024) ≤ (113240541 / 250000000) := by
  have h := checkLog_sound (w := (373 / 1675)) (n := 12)
    (lo := (452962163 / 1000000000)) (hi := (113240541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 651) = 1/(651 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-113240541 / 250000000) (-452962163 / 1000000000) (Real.log (651 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7199341 / 31250000) ≤ -Real.log (1000000 / 1259077) ∧
    -Real.log (1000000 / 1259077) ≤ (230378913 / 1000000000) := by
  have h := checkLog_sound (w := (259077 / 2259077)) (n := 12)
    (lo := (7199341 / 31250000)) (hi := (230378913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259077 / 1000000) = 1/(1000000 / 1259077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7199341 / 31250000) (230378913 / 1000000000) (Real.log (1259077 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1259077 / 1000000) = -Real.log (1000000 / 1259077) := by
    rw [show ((1259077 / 1000000) : ℝ) = ((1000000 / 1259077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (74964643 / 250000000) ≤ -Real.log (740923 / 1000000) ∧
    -Real.log (740923 / 1000000) ≤ (299858573 / 1000000000) := by
  have h := checkLog_sound (w := (259077 / 1740923)) (n := 12)
    (lo := (74964643 / 250000000)) (hi := (299858573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 740923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 740923) = 1/(740923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-299858573 / 1000000000) (-74964643 / 250000000) (Real.log (740923 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (3604919 / 15625000) ≤ -Real.log (2000 / 2519) ∧
    -Real.log (2000 / 2519) ≤ (230714817 / 1000000000) := by
  have h := checkLog_sound (w := (519 / 4519)) (n := 12)
    (lo := (3604919 / 15625000)) (hi := (230714817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2519 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2519 / 2000) = 1/(2000 / 2519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (3604919 / 15625000) (230714817 / 1000000000) (Real.log (2519 / 2000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2519 / 2000) = -Real.log (2000 / 2519) := by
    rw [show ((2519 / 2000) : ℝ) = ((2000 / 2519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (60085929 / 200000000) ≤ -Real.log (1481 / 2000) ∧
    -Real.log (1481 / 2000) ≤ (150214823 / 500000000) := by
  have h := checkLog_sound (w := (519 / 3481)) (n := 12)
    (lo := (60085929 / 200000000)) (hi := (150214823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1481) = 1/(1481 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-150214823 / 500000000) (-60085929 / 200000000) (Real.log (1481 / 2000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85573847 / 500000000) ≤ -Real.log (500000 / 593333) ∧
    -Real.log (500000 / 593333) ≤ (34229539 / 200000000) := by
  have h := checkLog_sound (w := (93333 / 1093333)) (n := 12)
    (lo := (85573847 / 500000000)) (hi := (34229539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593333 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593333 / 500000) = 1/(500000 / 593333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85573847 / 500000000) (34229539 / 200000000) (Real.log (593333 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (593333 / 500000) = -Real.log (500000 / 593333) := by
    rw [show ((593333 / 500000) : ℝ) = ((500000 / 593333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (206613429 / 1000000000) ≤ -Real.log (406667 / 500000) ∧
    -Real.log (406667 / 500000) ≤ (20661343 / 100000000) := by
  have h := checkLog_sound (w := (93333 / 906667)) (n := 12)
    (lo := (206613429 / 1000000000)) (hi := (20661343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406667) = 1/(406667 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-20661343 / 100000000) (-206613429 / 1000000000) (Real.log (406667 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (171413951 / 1000000000) ≤ -Real.log (500000 / 593491) ∧
    -Real.log (500000 / 593491) ≤ (2678343 / 15625000) := by
  have h := checkLog_sound (w := (93491 / 1093491)) (n := 12)
    (lo := (171413951 / 1000000000)) (hi := (2678343 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593491 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593491 / 500000) = 1/(500000 / 593491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (171413951 / 1000000000) (2678343 / 15625000) (Real.log (593491 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (593491 / 500000) = -Real.log (500000 / 593491) := by
    rw [show ((593491 / 500000) : ℝ) = ((500000 / 593491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (207002029 / 1000000000) ≤ -Real.log (406509 / 500000) ∧
    -Real.log (406509 / 500000) ≤ (20700203 / 100000000) := by
  have h := checkLog_sound (w := (93491 / 906509)) (n := 12)
    (lo := (207002029 / 1000000000)) (hi := (20700203 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406509) = 1/(406509 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-20700203 / 100000000) (-207002029 / 1000000000) (Real.log (406509 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (190893179 / 250000000) ≤ -Real.log (250000000000 / 536482334869) ∧
    -Real.log (250000000000 / 536482334869) ≤ (381786359 / 500000000) := by
  have h := checkLog_sound (w := (36482334869 / 1036482334869)) (n := 12)
    (lo := (1100399 / 15625000)) (hi := (70425537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((536482334869 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(536482334869 / 500000000000) = 1/(250000000000 / 536482334869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (190893179 / 250000000) (381786359 / 500000000) (Real.log (536482334869 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (536482334869 / 250000000000) = -Real.log (250000000000 / 536482334869) := by
    rw [show ((536482334869 / 250000000000) : ℝ) = ((250000000000 / 536482334869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3824621 / 5000000) ≤ -Real.log (250000000000 / 537207872079) ∧
    -Real.log (250000000000 / 537207872079) ≤ (382462101 / 500000000) := by
  have h := checkLog_sound (w := (37207872079 / 1037207872079)) (n := 12)
    (lo := (3588851 / 50000000)) (hi := (71777021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537207872079 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(537207872079 / 500000000000) = 1/(250000000000 / 537207872079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (3824621 / 5000000) (382462101 / 500000000) (Real.log (537207872079 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (537207872079 / 250000000000) = -Real.log (250000000000 / 537207872079) := by
    rw [show ((537207872079 / 250000000000) : ℝ) = ((250000000000 / 537207872079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (106047497 / 200000000) ≤ -Real.log (500000000000 / 849667914209) ∧
    -Real.log (500000000000 / 849667914209) ≤ (265118743 / 500000000) := by
  have h := checkLog_sound (w := (349667914209 / 1349667914209)) (n := 12)
    (lo := (106047497 / 200000000)) (hi := (265118743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849667914209 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849667914209 / 500000000000) = 1/(500000000000 / 849667914209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (106047497 / 200000000) (265118743 / 500000000) (Real.log (849667914209 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (849667914209 / 500000000000) = -Real.log (500000000000 / 849667914209) := by
    rw [show ((849667914209 / 500000000000) : ℝ) = ((500000000000 / 849667914209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (265572231 / 500000000) ≤ -Real.log (500000000000 / 850438892641) ∧
    -Real.log (500000000000 / 850438892641) ≤ (531144463 / 1000000000) := by
  have h := checkLog_sound (w := (350438892641 / 1350438892641)) (n := 12)
    (lo := (265572231 / 500000000)) (hi := (531144463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850438892641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850438892641 / 500000000000) = 1/(500000000000 / 850438892641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (265572231 / 500000000) (531144463 / 1000000000) (Real.log (850438892641 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (850438892641 / 500000000000) = -Real.log (500000000000 / 850438892641) := by
    rw [show ((850438892641 / 500000000000) : ℝ) = ((500000000000 / 850438892641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (94440281 / 250000000) ≤ -Real.log (7812500000 / 11398549827) ∧
    -Real.log (7812500000 / 11398549827) ≤ (3022089 / 8000000) := by
  have h := checkLog_sound (w := (3586049827 / 19211049827)) (n := 12)
    (lo := (94440281 / 250000000)) (hi := (3022089 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11398549827 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11398549827 / 7812500000) = 1/(7812500000 / 11398549827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (94440281 / 250000000) (3022089 / 8000000) (Real.log (11398549827 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11398549827 / 7812500000) = -Real.log (7812500000 / 11398549827) := by
    rw [show ((11398549827 / 7812500000) : ℝ) = ((7812500000 / 11398549827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (18920799 / 50000000) ≤ -Real.log (250000000000 / 364992533991) ∧
    -Real.log (250000000000 / 364992533991) ≤ (378415981 / 1000000000) := by
  have h := checkLog_sound (w := (114992533991 / 614992533991)) (n := 12)
    (lo := (18920799 / 50000000)) (hi := (378415981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364992533991 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364992533991 / 250000000000) = 1/(250000000000 / 364992533991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (18920799 / 50000000) (378415981 / 1000000000) (Real.log (364992533991 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (364992533991 / 250000000000) = -Real.log (250000000000 / 364992533991) := by
    rw [show ((364992533991 / 250000000000) : ℝ) = ((250000000000 / 364992533991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17794039 / 500000000) ≤ -Real.log (241259432919 / 250000000000) ∧
    -Real.log (241259432919 / 250000000000) ≤ (35588079 / 1000000000) := by
  have h := checkLog_sound (w := (8740567081 / 491259432919)) (n := 12)
    (lo := (17794039 / 500000000)) (hi := (35588079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241259432919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241259432919) = 1/(241259432919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-35588079 / 1000000000) (-17794039 / 500000000) (Real.log (241259432919 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7093147 / 200000000) ≤ -Real.log (241288951111 / 250000000000) ∧
    -Real.log (241288951111 / 250000000000) ≤ (4433217 / 125000000) := by
  have h := checkLog_sound (w := (8711048889 / 491288951111)) (n := 12)
    (lo := (7093147 / 200000000)) (hi := (4433217 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241288951111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241288951111) = 1/(241288951111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4433217 / 125000000) (-7093147 / 200000000) (Real.log (241288951111 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell195

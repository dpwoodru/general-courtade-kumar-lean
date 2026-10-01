import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0382
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

theorem reflection_log_1_neg : (102266981 / 500000000) ≤ -Real.log (2560 / 3141) ∧
    -Real.log (2560 / 3141) ≤ (204533963 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 5701)) (n := 12)
    (lo := (102266981 / 500000000)) (hi := (204533963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3141 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3141 / 2560) = 1/(2560 / 3141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (102266981 / 500000000) (204533963 / 1000000000) (Real.log (3141 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3141 / 2560) = -Real.log (2560 / 3141) := by
    rw [show ((3141 / 2560) : ℝ) = ((2560 / 3141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (257415591 / 1000000000) ≤ -Real.log (1979 / 2560) ∧
    -Real.log (1979 / 2560) ≤ (32176949 / 125000000) := by
  have h := checkLog_sound (w := (581 / 4539)) (n := 12)
    (lo := (257415591 / 1000000000)) (hi := (32176949 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1979) = 1/(1979 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-32176949 / 125000000) (-257415591 / 1000000000) (Real.log (1979 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (51073789 / 250000000) ≤ -Real.log (10240 / 12561) ∧
    -Real.log (10240 / 12561) ≤ (204295157 / 1000000000) := by
  have h := checkLog_sound (w := (2321 / 22801)) (n := 12)
    (lo := (51073789 / 250000000)) (hi := (204295157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12561 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12561 / 10240) = 1/(10240 / 12561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (51073789 / 250000000) (204295157 / 1000000000) (Real.log (12561 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12561 / 10240) = -Real.log (10240 / 12561) := by
    rw [show ((12561 / 10240) : ℝ) = ((10240 / 12561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (64259171 / 250000000) ≤ -Real.log (7919 / 10240) ∧
    -Real.log (7919 / 10240) ≤ (51407337 / 200000000) := by
  have h := checkLog_sound (w := (2321 / 18159)) (n := 12)
    (lo := (64259171 / 250000000)) (hi := (51407337 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7919) = 1/(7919 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-51407337 / 200000000) (-64259171 / 250000000) (Real.log (7919 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (374253899 / 1000000000) ≤ -Real.log (1280 / 1861) ∧
    -Real.log (1280 / 1861) ≤ (3742539 / 10000000) := by
  have h := checkLog_sound (w := (581 / 3141)) (n := 12)
    (lo := (374253899 / 1000000000)) (hi := (3742539 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1861 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1861 / 1280) = 1/(1280 / 1861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (374253899 / 1000000000) (3742539 / 10000000) (Real.log (1861 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1861 / 1280) = -Real.log (1280 / 1861) := by
    rw [show ((1861 / 1280) : ℝ) = ((1280 / 1861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (302482307 / 500000000) ≤ -Real.log (699 / 1280) ∧
    -Real.log (699 / 1280) ≤ (120992923 / 200000000) := by
  have h := checkLog_sound (w := (581 / 1979)) (n := 12)
    (lo := (302482307 / 500000000)) (hi := (120992923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 699) = 1/(699 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-120992923 / 200000000) (-302482307 / 500000000) (Real.log (699 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (373850809 / 1000000000) ≤ -Real.log (5120 / 7441) ∧
    -Real.log (5120 / 7441) ≤ (37385081 / 100000000) := by
  have h := checkLog_sound (w := (2321 / 12561)) (n := 12)
    (lo := (373850809 / 1000000000)) (hi := (37385081 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7441 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7441 / 5120) = 1/(5120 / 7441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (373850809 / 1000000000) (37385081 / 100000000) (Real.log (7441 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7441 / 5120) = -Real.log (5120 / 7441) := by
    rw [show ((7441 / 5120) : ℝ) = ((5120 / 7441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (150973057 / 250000000) ≤ -Real.log (2799 / 5120) ∧
    -Real.log (2799 / 5120) ≤ (603892229 / 1000000000) := by
  have h := checkLog_sound (w := (2321 / 7919)) (n := 12)
    (lo := (150973057 / 250000000)) (hi := (603892229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2799) = 1/(2799 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-603892229 / 1000000000) (-150973057 / 250000000) (Real.log (2799 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (280319787 / 1000000000) ≤ -Real.log (1000000 / 1323553) ∧
    -Real.log (1000000 / 1323553) ≤ (70079947 / 250000000) := by
  have h := checkLog_sound (w := (323553 / 2323553)) (n := 12)
    (lo := (280319787 / 1000000000)) (hi := (70079947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323553 / 1000000) = 1/(1000000 / 1323553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (280319787 / 1000000000) (70079947 / 250000000) (Real.log (1323553 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1323553 / 1000000) = -Real.log (1000000 / 1323553) := by
    rw [show ((1323553 / 1000000) : ℝ) = ((1000000 / 1323553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (195450589 / 500000000) ≤ -Real.log (676447 / 1000000) ∧
    -Real.log (676447 / 1000000) ≤ (390901179 / 1000000000) := by
  have h := checkLog_sound (w := (323553 / 1676447)) (n := 12)
    (lo := (195450589 / 500000000)) (hi := (390901179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 676447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 676447) = 1/(676447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-390901179 / 1000000000) (-195450589 / 500000000) (Real.log (676447 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (140321553 / 500000000) ≤ -Real.log (1000000 / 1323981) ∧
    -Real.log (1000000 / 1323981) ≤ (280643107 / 1000000000) := by
  have h := checkLog_sound (w := (323981 / 2323981)) (n := 12)
    (lo := (140321553 / 500000000)) (hi := (280643107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323981 / 1000000) = 1/(1000000 / 1323981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (140321553 / 500000000) (280643107 / 1000000000) (Real.log (1323981 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1323981 / 1000000) = -Real.log (1000000 / 1323981) := by
    rw [show ((1323981 / 1000000) : ℝ) = ((1000000 / 1323981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (24470881 / 62500000) ≤ -Real.log (676019 / 1000000) ∧
    -Real.log (676019 / 1000000) ≤ (391534097 / 1000000000) := by
  have h := checkLog_sound (w := (323981 / 1676019)) (n := 12)
    (lo := (24470881 / 62500000)) (hi := (391534097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 676019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 676019) = 1/(676019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-391534097 / 1000000000) (-24470881 / 62500000) (Real.log (676019 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (52892003 / 250000000) ≤ -Real.log (500000 / 617807) ∧
    -Real.log (500000 / 617807) ≤ (211568013 / 1000000000) := by
  have h := checkLog_sound (w := (117807 / 1117807)) (n := 12)
    (lo := (52892003 / 250000000)) (hi := (211568013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617807 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(617807 / 500000) = 1/(500000 / 617807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (52892003 / 250000000) (211568013 / 1000000000) (Real.log (617807 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (617807 / 500000) = -Real.log (500000 / 617807) := by
    rw [show ((617807 / 500000) : ℝ) = ((500000 / 617807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (268682381 / 1000000000) ≤ -Real.log (382193 / 500000) ∧
    -Real.log (382193 / 500000) ≤ (134341191 / 500000000) := by
  have h := checkLog_sound (w := (117807 / 882193)) (n := 12)
    (lo := (268682381 / 1000000000)) (hi := (134341191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 382193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 382193) = 1/(382193 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-134341191 / 500000000) (-268682381 / 1000000000) (Real.log (382193 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (4236701 / 20000000) ≤ -Real.log (125000 / 154493) ∧
    -Real.log (125000 / 154493) ≤ (211835051 / 1000000000) := by
  have h := checkLog_sound (w := (29493 / 279493)) (n := 12)
    (lo := (4236701 / 20000000)) (hi := (211835051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154493 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154493 / 125000) = 1/(125000 / 154493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4236701 / 20000000) (211835051 / 1000000000) (Real.log (154493 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (154493 / 125000) = -Real.log (125000 / 154493) := by
    rw [show ((154493 / 125000) : ℝ) = ((125000 / 154493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (134557097 / 500000000) ≤ -Real.log (95507 / 125000) ∧
    -Real.log (95507 / 125000) ≤ (53822839 / 200000000) := by
  have h := checkLog_sound (w := (29493 / 220507)) (n := 12)
    (lo := (134557097 / 500000000)) (hi := (53822839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 95507) = 1/(95507 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-53822839 / 200000000) (-134557097 / 500000000) (Real.log (95507 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (335610483 / 500000000) ≤ -Real.log (125000000000 / 244578104419) ∧
    -Real.log (125000000000 / 244578104419) ≤ (671220967 / 1000000000) := by
  have h := checkLog_sound (w := (119578104419 / 369578104419)) (n := 12)
    (lo := (335610483 / 500000000)) (hi := (671220967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244578104419 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244578104419 / 125000000000) = 1/(125000000000 / 244578104419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (335610483 / 500000000) (671220967 / 1000000000) (Real.log (244578104419 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (244578104419 / 125000000000) = -Real.log (125000000000 / 244578104419) := by
    rw [show ((244578104419 / 125000000000) : ℝ) = ((125000000000 / 244578104419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (672177203 / 1000000000) ≤ -Real.log (250000000000 / 489624182161) ∧
    -Real.log (250000000000 / 489624182161) ≤ (168044301 / 250000000) := by
  have h := checkLog_sound (w := (239624182161 / 739624182161)) (n := 12)
    (lo := (672177203 / 1000000000)) (hi := (168044301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489624182161 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489624182161 / 250000000000) = 1/(250000000000 / 489624182161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (672177203 / 1000000000) (168044301 / 250000000) (Real.log (489624182161 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (489624182161 / 250000000000) = -Real.log (250000000000 / 489624182161) := by
    rw [show ((489624182161 / 250000000000) : ℝ) = ((250000000000 / 489624182161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (240125197 / 500000000) ≤ -Real.log (500000000000 / 808239554361) ∧
    -Real.log (500000000000 / 808239554361) ≤ (96050079 / 200000000) := by
  have h := checkLog_sound (w := (308239554361 / 1308239554361)) (n := 12)
    (lo := (240125197 / 500000000)) (hi := (96050079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808239554361 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808239554361 / 500000000000) = 1/(500000000000 / 808239554361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (240125197 / 500000000) (96050079 / 200000000) (Real.log (808239554361 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (808239554361 / 500000000000) = -Real.log (500000000000 / 808239554361) := by
    rw [show ((808239554361 / 500000000000) : ℝ) = ((500000000000 / 808239554361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (120237311 / 250000000) ≤ -Real.log (3125000000 / 5055028689) ∧
    -Real.log (3125000000 / 5055028689) ≤ (96189849 / 200000000) := by
  have h := checkLog_sound (w := (1930028689 / 8180028689)) (n := 12)
    (lo := (120237311 / 250000000)) (hi := (96189849 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5055028689 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5055028689 / 3125000000) = 1/(3125000000 / 5055028689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (120237311 / 250000000) (96189849 / 200000000) (Real.log (5055028689 / 3125000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5055028689 / 3125000000) = -Real.log (3125000000 / 5055028689) := by
    rw [show ((5055028689 / 3125000000) : ℝ) = ((3125000000 / 5055028689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0382

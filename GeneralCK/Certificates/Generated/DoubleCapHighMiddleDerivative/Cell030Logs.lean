import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell030
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

theorem reflection_log_1_neg : (118785117 / 500000000) ≤ -Real.log (5120 / 6493) ∧
    -Real.log (5120 / 6493) ≤ (47514047 / 200000000) := by
  have h := checkLog_sound (w := (1373 / 11613)) (n := 12)
    (lo := (118785117 / 500000000)) (hi := (47514047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6493 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6493 / 5120) = 1/(5120 / 6493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (118785117 / 500000000) (47514047 / 200000000) (Real.log (6493 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6493 / 5120) = -Real.log (5120 / 6493) := by
    rw [show ((6493 / 5120) : ℝ) = ((5120 / 6493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (312198919 / 1000000000) ≤ -Real.log (3747 / 5120) ∧
    -Real.log (3747 / 5120) ≤ (7804973 / 25000000) := by
  have h := checkLog_sound (w := (1373 / 8867)) (n := 12)
    (lo := (312198919 / 1000000000)) (hi := (7804973 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3747) = 1/(3747 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7804973 / 25000000) (-312198919 / 1000000000) (Real.log (3747 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (237108091 / 1000000000) ≤ -Real.log (512 / 649) ∧
    -Real.log (512 / 649) ≤ (59277023 / 250000000) := by
  have h := checkLog_sound (w := (137 / 1161)) (n := 12)
    (lo := (237108091 / 1000000000)) (hi := (59277023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649 / 512) = 1/(512 / 649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (237108091 / 1000000000) (59277023 / 250000000) (Real.log (649 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (649 / 512) = -Real.log (512 / 649) := by
    rw [show ((649 / 512) : ℝ) = ((512 / 649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (311398599 / 1000000000) ≤ -Real.log (375 / 512) ∧
    -Real.log (375 / 512) ≤ (1556993 / 5000000) := by
  have h := checkLog_sound (w := (137 / 887)) (n := 12)
    (lo := (311398599 / 1000000000)) (hi := (1556993 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 375) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 375) = 1/(375 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1556993 / 5000000) (-311398599 / 1000000000) (Real.log (375 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (173775139 / 1000000000) ≤ -Real.log (250000 / 297447) ∧
    -Real.log (250000 / 297447) ≤ (8688757 / 50000000) := by
  have h := checkLog_sound (w := (47447 / 547447)) (n := 12)
    (lo := (173775139 / 1000000000)) (hi := (8688757 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297447 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297447 / 250000) = 1/(250000 / 297447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (173775139 / 1000000000) (8688757 / 50000000) (Real.log (297447 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (297447 / 250000) = -Real.log (250000 / 297447) := by
    rw [show ((297447 / 250000) : ℝ) = ((250000 / 297447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (210459337 / 1000000000) ≤ -Real.log (202553 / 250000) ∧
    -Real.log (202553 / 250000) ≤ (105229669 / 500000000) := by
  have h := checkLog_sound (w := (47447 / 452553)) (n := 12)
    (lo := (210459337 / 1000000000)) (hi := (105229669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202553) = 1/(202553 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-105229669 / 500000000) (-210459337 / 1000000000) (Real.log (202553 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (174127241 / 1000000000) ≤ -Real.log (1000000 / 1190207) ∧
    -Real.log (1000000 / 1190207) ≤ (87063621 / 500000000) := by
  have h := checkLog_sound (w := (190207 / 2190207)) (n := 12)
    (lo := (174127241 / 1000000000)) (hi := (87063621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1190207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1190207 / 1000000) = 1/(1000000 / 1190207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (174127241 / 1000000000) (87063621 / 500000000) (Real.log (1190207 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1190207 / 1000000) = -Real.log (1000000 / 1190207) := by
    rw [show ((1190207 / 1000000) : ℝ) = ((1000000 / 1190207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (210976619 / 1000000000) ≤ -Real.log (809793 / 1000000) ∧
    -Real.log (809793 / 1000000) ≤ (10548831 / 50000000) := by
  have h := checkLog_sound (w := (190207 / 1809793)) (n := 12)
    (lo := (210976619 / 1000000000)) (hi := (10548831 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 809793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 809793) = 1/(809793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-10548831 / 50000000) (-210976619 / 1000000000) (Real.log (809793 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (31779939 / 250000000) ≤ -Real.log (1000000 / 1135553) ∧
    -Real.log (1000000 / 1135553) ≤ (127119757 / 1000000000) := by
  have h := checkLog_sound (w := (135553 / 2135553)) (n := 12)
    (lo := (31779939 / 250000000)) (hi := (127119757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1135553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1135553 / 1000000) = 1/(1000000 / 1135553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (31779939 / 250000000) (127119757 / 1000000000) (Real.log (1135553 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1135553 / 1000000) = -Real.log (1000000 / 1135553) := by
    rw [show ((1135553 / 1000000) : ℝ) = ((1000000 / 1135553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72832641 / 500000000) ≤ -Real.log (864447 / 1000000) ∧
    -Real.log (864447 / 1000000) ≤ (145665283 / 1000000000) := by
  have h := checkLog_sound (w := (135553 / 1864447)) (n := 12)
    (lo := (72832641 / 500000000)) (hi := (145665283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 864447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 864447) = 1/(864447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-145665283 / 1000000000) (-72832641 / 500000000) (Real.log (864447 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15923649 / 125000000) ≤ -Real.log (1000000 / 1135859) ∧
    -Real.log (1000000 / 1135859) ≤ (127389193 / 1000000000) := by
  have h := checkLog_sound (w := (135859 / 2135859)) (n := 12)
    (lo := (15923649 / 125000000)) (hi := (127389193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1135859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1135859 / 1000000) = 1/(1000000 / 1135859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15923649 / 125000000) (127389193 / 1000000000) (Real.log (1135859 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1135859 / 1000000) = -Real.log (1000000 / 1135859) := by
    rw [show ((1135859 / 1000000) : ℝ) = ((1000000 / 1135859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (146019329 / 1000000000) ≤ -Real.log (864141 / 1000000) ∧
    -Real.log (864141 / 1000000) ≤ (14601933 / 100000000) := by
  have h := checkLog_sound (w := (135859 / 1864141)) (n := 12)
    (lo := (146019329 / 1000000000)) (hi := (14601933 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 864141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 864141) = 1/(864141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-14601933 / 100000000) (-146019329 / 1000000000) (Real.log (864141 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (54850669 / 100000000) ≤ -Real.log (500000000000 / 865333333333) ∧
    -Real.log (500000000000 / 865333333333) ≤ (548506691 / 1000000000) := by
  have h := checkLog_sound (w := (365333333333 / 1365333333333)) (n := 12)
    (lo := (54850669 / 100000000)) (hi := (548506691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((865333333333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(865333333333 / 500000000000) = 1/(500000000000 / 865333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (54850669 / 100000000) (548506691 / 1000000000) (Real.log (865333333333 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (865333333333 / 500000000000) = -Real.log (500000000000 / 865333333333) := by
    rw [show ((865333333333 / 500000000000) : ℝ) = ((500000000000 / 865333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (549769153 / 1000000000) ≤ -Real.log (500000000000 / 866426474513) ∧
    -Real.log (500000000000 / 866426474513) ≤ (274884577 / 500000000) := by
  have h := checkLog_sound (w := (366426474513 / 1366426474513)) (n := 12)
    (lo := (549769153 / 1000000000)) (hi := (274884577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((866426474513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(866426474513 / 500000000000) = 1/(500000000000 / 866426474513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (549769153 / 1000000000) (274884577 / 500000000) (Real.log (866426474513 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (866426474513 / 500000000000) = -Real.log (500000000000 / 866426474513) := by
    rw [show ((866426474513 / 500000000000) : ℝ) = ((500000000000 / 866426474513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (384234477 / 1000000000) ≤ -Real.log (500000000000 / 734244864307) ∧
    -Real.log (500000000000 / 734244864307) ≤ (192117239 / 500000000) := by
  have h := checkLog_sound (w := (234244864307 / 1234244864307)) (n := 12)
    (lo := (384234477 / 1000000000)) (hi := (192117239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734244864307 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734244864307 / 500000000000) = 1/(500000000000 / 734244864307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (384234477 / 1000000000) (192117239 / 500000000) (Real.log (734244864307 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (734244864307 / 500000000000) = -Real.log (500000000000 / 734244864307) := by
    rw [show ((734244864307 / 500000000000) : ℝ) = ((500000000000 / 734244864307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (385103861 / 1000000000) ≤ -Real.log (50000000000 / 73488348257) ∧
    -Real.log (50000000000 / 73488348257) ≤ (192551931 / 500000000) := by
  have h := checkLog_sound (w := (23488348257 / 123488348257)) (n := 12)
    (lo := (385103861 / 1000000000)) (hi := (192551931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73488348257 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73488348257 / 50000000000) = 1/(50000000000 / 73488348257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (385103861 / 1000000000) (192551931 / 500000000) (Real.log (73488348257 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (73488348257 / 50000000000) = -Real.log (50000000000 / 73488348257) := by
    rw [show ((73488348257 / 50000000000) : ℝ) = ((50000000000 / 73488348257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (272785039 / 1000000000) ≤ -Real.log (500000000000 / 656808919459) ∧
    -Real.log (500000000000 / 656808919459) ≤ (3409813 / 12500000) := by
  have h := checkLog_sound (w := (156808919459 / 1156808919459)) (n := 12)
    (lo := (272785039 / 1000000000)) (hi := (3409813 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656808919459 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(656808919459 / 500000000000) = 1/(500000000000 / 656808919459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (272785039 / 1000000000) (3409813 / 12500000) (Real.log (656808919459 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (656808919459 / 500000000000) = -Real.log (500000000000 / 656808919459) := by
    rw [show ((656808919459 / 500000000000) : ℝ) = ((500000000000 / 656808919459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (273408521 / 1000000000) ≤ -Real.log (500000000000 / 657218555769) ∧
    -Real.log (500000000000 / 657218555769) ≤ (136704261 / 500000000) := by
  have h := checkLog_sound (w := (157218555769 / 1157218555769)) (n := 12)
    (lo := (273408521 / 1000000000)) (hi := (136704261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657218555769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657218555769 / 500000000000) = 1/(500000000000 / 657218555769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (273408521 / 1000000000) (136704261 / 500000000) (Real.log (657218555769 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (657218555769 / 500000000000) = -Real.log (500000000000 / 657218555769) := by
    rw [show ((657218555769 / 500000000000) : ℝ) = ((500000000000 / 657218555769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2328767 / 125000000) ≤ -Real.log (981542332119 / 1000000000000) ∧
    -Real.log (981542332119 / 1000000000000) ≤ (18630137 / 1000000000) := by
  have h := checkLog_sound (w := (18457667881 / 1981542332119)) (n := 12)
    (lo := (2328767 / 125000000)) (hi := (18630137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981542332119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981542332119) = 1/(981542332119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18630137 / 1000000000) (-2328767 / 125000000) (Real.log (981542332119 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (741821 / 40000000) ≤ -Real.log (981625384191 / 1000000000000) ∧
    -Real.log (981625384191 / 1000000000000) ≤ (9272763 / 500000000) := by
  have h := checkLog_sound (w := (18374615809 / 1981625384191)) (n := 12)
    (lo := (741821 / 40000000)) (hi := (9272763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981625384191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981625384191) = 1/(981625384191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9272763 / 500000000) (-741821 / 40000000) (Real.log (981625384191 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell030

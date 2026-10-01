import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0422
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

theorem reflection_log_1_neg : (194936959 / 1000000000) ≤ -Real.log (2560 / 3111) ∧
    -Real.log (2560 / 3111) ≤ (304589 / 1562500) := by
  have h := checkLog_sound (w := (551 / 5671)) (n := 12)
    (lo := (194936959 / 1000000000)) (hi := (304589 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3111 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3111 / 2560) = 1/(2560 / 3111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (194936959 / 1000000000) (304589 / 1562500) (Real.log (3111 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3111 / 2560) = -Real.log (2560 / 3111) := by
    rw [show ((3111 / 2560) : ℝ) = ((2560 / 3111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (60592543 / 250000000) ≤ -Real.log (2009 / 2560) ∧
    -Real.log (2009 / 2560) ≤ (242370173 / 1000000000) := by
  have h := checkLog_sound (w := (551 / 4569)) (n := 12)
    (lo := (60592543 / 250000000)) (hi := (242370173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2009) = 1/(2009 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-242370173 / 1000000000) (-60592543 / 250000000) (Real.log (2009 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (3893917 / 20000000) ≤ -Real.log (10240 / 12441) ∧
    -Real.log (10240 / 12441) ≤ (194695851 / 1000000000) := by
  have h := checkLog_sound (w := (2201 / 22681)) (n := 12)
    (lo := (3893917 / 20000000)) (hi := (194695851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12441 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12441 / 10240) = 1/(10240 / 12441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (3893917 / 20000000) (194695851 / 1000000000) (Real.log (12441 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12441 / 10240) = -Real.log (10240 / 12441) := by
    rw [show ((12441 / 10240) : ℝ) = ((10240 / 12441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (120998461 / 500000000) ≤ -Real.log (8039 / 10240) ∧
    -Real.log (8039 / 10240) ≤ (241996923 / 1000000000) := by
  have h := checkLog_sound (w := (2201 / 18279)) (n := 12)
    (lo := (120998461 / 500000000)) (hi := (241996923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8039) = 1/(8039 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-241996923 / 1000000000) (-120998461 / 500000000) (Real.log (8039 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (358002187 / 1000000000) ≤ -Real.log (1280 / 1831) ∧
    -Real.log (1280 / 1831) ≤ (89500547 / 250000000) := by
  have h := checkLog_sound (w := (551 / 3111)) (n := 12)
    (lo := (358002187 / 1000000000)) (hi := (89500547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1831 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1831 / 1280) = 1/(1280 / 1831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (358002187 / 1000000000) (89500547 / 250000000) (Real.log (1831 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1831 / 1280) = -Real.log (1280 / 1831) := by
    rw [show ((1831 / 1280) : ℝ) = ((1280 / 1831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (70367703 / 125000000) ≤ -Real.log (729 / 1280) ∧
    -Real.log (729 / 1280) ≤ (4503533 / 8000000) := by
  have h := checkLog_sound (w := (551 / 2009)) (n := 12)
    (lo := (70367703 / 125000000)) (hi := (4503533 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 729) = 1/(729 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4503533 / 8000000) (-70367703 / 125000000) (Real.log (729 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (357592491 / 1000000000) ≤ -Real.log (5120 / 7321) ∧
    -Real.log (5120 / 7321) ≤ (89398123 / 250000000) := by
  have h := checkLog_sound (w := (2201 / 12441)) (n := 12)
    (lo := (357592491 / 1000000000)) (hi := (89398123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7321 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7321 / 5120) = 1/(5120 / 7321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (357592491 / 1000000000) (89398123 / 250000000) (Real.log (7321 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7321 / 5120) = -Real.log (5120 / 7321) := by
    rw [show ((7321 / 5120) : ℝ) = ((5120 / 7321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (561913347 / 1000000000) ≤ -Real.log (2919 / 5120) ∧
    -Real.log (2919 / 5120) ≤ (140478337 / 250000000) := by
  have h := checkLog_sound (w := (2201 / 8039)) (n := 12)
    (lo := (561913347 / 1000000000)) (hi := (140478337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2919) = 1/(2919 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-140478337 / 250000000) (-561913347 / 1000000000) (Real.log (2919 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (26736099 / 100000000) ≤ -Real.log (62500 / 81657) ∧
    -Real.log (62500 / 81657) ≤ (267360991 / 1000000000) := by
  have h := checkLog_sound (w := (19157 / 144157)) (n := 12)
    (lo := (26736099 / 100000000)) (hi := (267360991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81657 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81657 / 62500) = 1/(62500 / 81657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (26736099 / 100000000) (267360991 / 1000000000) (Real.log (81657 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (81657 / 62500) = -Real.log (62500 / 81657) := by
    rw [show ((81657 / 62500) : ℝ) = ((62500 / 81657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (183010671 / 500000000) ≤ -Real.log (43343 / 62500) ∧
    -Real.log (43343 / 62500) ≤ (366021343 / 1000000000) := by
  have h := checkLog_sound (w := (19157 / 105843)) (n := 12)
    (lo := (183010671 / 500000000)) (hi := (366021343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 43343) = 1/(43343 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-366021343 / 1000000000) (-183010671 / 500000000) (Real.log (43343 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (267687761 / 1000000000) ≤ -Real.log (1000000 / 1306939) ∧
    -Real.log (1000000 / 1306939) ≤ (133843881 / 500000000) := by
  have h := checkLog_sound (w := (306939 / 2306939)) (n := 12)
    (lo := (267687761 / 1000000000)) (hi := (133843881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306939 / 1000000) = 1/(1000000 / 1306939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (267687761 / 1000000000) (133843881 / 500000000) (Real.log (1306939 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1306939 / 1000000) = -Real.log (1000000 / 1306939) := by
    rw [show ((1306939 / 1000000) : ℝ) = ((1000000 / 1306939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18331863 / 50000000) ≤ -Real.log (693061 / 1000000) ∧
    -Real.log (693061 / 1000000) ≤ (366637261 / 1000000000) := by
  have h := checkLog_sound (w := (306939 / 1693061)) (n := 12)
    (lo := (18331863 / 50000000)) (hi := (366637261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693061) = 1/(693061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-366637261 / 1000000000) (-18331863 / 50000000) (Real.log (693061 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (25114799 / 125000000) ≤ -Real.log (40000 / 48901) ∧
    -Real.log (40000 / 48901) ≤ (200918393 / 1000000000) := by
  have h := checkLog_sound (w := (8901 / 88901)) (n := 12)
    (lo := (25114799 / 125000000)) (hi := (200918393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48901 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48901 / 40000) = 1/(40000 / 48901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (25114799 / 125000000) (200918393 / 1000000000) (Real.log (48901 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (48901 / 40000) = -Real.log (40000 / 48901) := by
    rw [show ((48901 / 40000) : ℝ) = ((40000 / 48901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (251703789 / 1000000000) ≤ -Real.log (31099 / 40000) ∧
    -Real.log (31099 / 40000) ≤ (25170379 / 100000000) := by
  have h := checkLog_sound (w := (8901 / 71099)) (n := 12)
    (lo := (251703789 / 1000000000)) (hi := (25170379 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31099) = 1/(31099 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-25170379 / 100000000) (-251703789 / 1000000000) (Real.log (31099 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (201185017 / 1000000000) ≤ -Real.log (1000000 / 1222851) ∧
    -Real.log (1000000 / 1222851) ≤ (100592509 / 500000000) := by
  have h := checkLog_sound (w := (222851 / 2222851)) (n := 12)
    (lo := (201185017 / 1000000000)) (hi := (100592509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222851 / 1000000) = 1/(1000000 / 1222851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (201185017 / 1000000000) (100592509 / 500000000) (Real.log (1222851 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1222851 / 1000000) = -Real.log (1000000 / 1222851) := by
    rw [show ((1222851 / 1000000) : ℝ) = ((1000000 / 1222851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (252123183 / 1000000000) ≤ -Real.log (777149 / 1000000) ∧
    -Real.log (777149 / 1000000) ≤ (15757699 / 62500000) := by
  have h := checkLog_sound (w := (222851 / 1777149)) (n := 12)
    (lo := (252123183 / 1000000000)) (hi := (15757699 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777149) = 1/(777149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-15757699 / 62500000) (-252123183 / 1000000000) (Real.log (777149 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (633382333 / 1000000000) ≤ -Real.log (500000000000 / 941986018503) ∧
    -Real.log (500000000000 / 941986018503) ≤ (316691167 / 500000000) := by
  have h := checkLog_sound (w := (441986018503 / 1441986018503)) (n := 12)
    (lo := (633382333 / 1000000000)) (hi := (316691167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941986018503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941986018503 / 500000000000) = 1/(500000000000 / 941986018503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (633382333 / 1000000000) (316691167 / 500000000) (Real.log (941986018503 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (941986018503 / 500000000000) = -Real.log (500000000000 / 941986018503) := by
    rw [show ((941986018503 / 500000000000) : ℝ) = ((500000000000 / 941986018503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (317162511 / 500000000) ≤ -Real.log (250000000000 / 471437218369) ∧
    -Real.log (250000000000 / 471437218369) ≤ (634325023 / 1000000000) := by
  have h := checkLog_sound (w := (221437218369 / 721437218369)) (n := 12)
    (lo := (317162511 / 500000000)) (hi := (634325023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471437218369 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471437218369 / 250000000000) = 1/(250000000000 / 471437218369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (317162511 / 500000000) (634325023 / 1000000000) (Real.log (471437218369 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (471437218369 / 250000000000) = -Real.log (250000000000 / 471437218369) := by
    rw [show ((471437218369 / 250000000000) : ℝ) = ((250000000000 / 471437218369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (452622181 / 1000000000) ≤ -Real.log (100000000000 / 157242998167) ∧
    -Real.log (100000000000 / 157242998167) ≤ (226311091 / 500000000) := by
  have h := checkLog_sound (w := (57242998167 / 257242998167)) (n := 12)
    (lo := (452622181 / 1000000000)) (hi := (226311091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157242998167 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157242998167 / 100000000000) = 1/(100000000000 / 157242998167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (452622181 / 1000000000) (226311091 / 500000000) (Real.log (157242998167 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (157242998167 / 100000000000) = -Real.log (100000000000 / 157242998167) := by
    rw [show ((157242998167 / 100000000000) : ℝ) = ((100000000000 / 157242998167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (453308201 / 1000000000) ≤ -Real.log (100000000000 / 157350906969) ∧
    -Real.log (100000000000 / 157350906969) ≤ (226654101 / 500000000) := by
  have h := checkLog_sound (w := (57350906969 / 257350906969)) (n := 12)
    (lo := (453308201 / 1000000000)) (hi := (226654101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157350906969 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157350906969 / 100000000000) = 1/(100000000000 / 157350906969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (453308201 / 1000000000) (226654101 / 500000000) (Real.log (157350906969 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (157350906969 / 100000000000) = -Real.log (100000000000 / 157350906969) := by
    rw [show ((157350906969 / 100000000000) : ℝ) = ((100000000000 / 157350906969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0422

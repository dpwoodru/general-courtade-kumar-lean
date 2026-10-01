import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0128
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

theorem reflection_log_1_neg : (309607903 / 1000000000) ≤ -Real.log (2560 / 3489) ∧
    -Real.log (2560 / 3489) ≤ (9675247 / 31250000) := by
  have h := checkLog_sound (w := (929 / 6049)) (n := 12)
    (lo := (309607903 / 1000000000)) (hi := (9675247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3489 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3489 / 2560) = 1/(2560 / 3489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (309607903 / 1000000000) (9675247 / 31250000) (Real.log (3489 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3489 / 2560) = -Real.log (2560 / 3489) := by
    rw [show ((3489 / 2560) : ℝ) = ((2560 / 3489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (225406967 / 500000000) ≤ -Real.log (1631 / 2560) ∧
    -Real.log (1631 / 2560) ≤ (90162787 / 200000000) := by
  have h := checkLog_sound (w := (929 / 4191)) (n := 12)
    (lo := (225406967 / 500000000)) (hi := (90162787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1631) = 1/(1631 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-90162787 / 200000000) (-225406967 / 500000000) (Real.log (1631 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (38593461 / 125000000) ≤ -Real.log (1280 / 1743) ∧
    -Real.log (1280 / 1743) ≤ (308747689 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 3023)) (n := 12)
    (lo := (38593461 / 125000000)) (hi := (308747689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1743 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1743 / 1280) = 1/(1280 / 1743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (38593461 / 125000000) (308747689 / 1000000000) (Real.log (1743 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1743 / 1280) = -Real.log (1280 / 1743) := by
    rw [show ((1743 / 1280) : ℝ) = ((1280 / 1743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (224488131 / 500000000) ≤ -Real.log (817 / 1280) ∧
    -Real.log (817 / 1280) ≤ (448976263 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2097)) (n := 12)
    (lo := (224488131 / 500000000)) (hi := (448976263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 817) = 1/(817 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-448976263 / 1000000000) (-224488131 / 500000000) (Real.log (817 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (272839923 / 500000000) ≤ -Real.log (1280 / 2209) ∧
    -Real.log (1280 / 2209) ≤ (545679847 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 3489)) (n := 12)
    (lo := (272839923 / 500000000)) (hi := (545679847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2209 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2209 / 1280) = 1/(1280 / 2209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (272839923 / 500000000) (545679847 / 1000000000) (Real.log (2209 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2209 / 1280) = -Real.log (1280 / 2209) := by
    rw [show ((2209 / 1280) : ℝ) = ((1280 / 2209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (323457283 / 250000000) ≤ -Real.log (351 / 1280) ∧
    -Real.log (351 / 1280) ≤ (646914567 / 500000000) := by
  have h := checkLog_sound (w := (289 / 991)) (n := 12)
    (lo := (18771311 / 31250000)) (hi := (600681953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 351) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 351) = 1/(351 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-646914567 / 500000000) (-323457283 / 250000000) (Real.log (351 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (272160421 / 500000000) ≤ -Real.log (640 / 1103) ∧
    -Real.log (640 / 1103) ≤ (544320843 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 1743)) (n := 12)
    (lo := (272160421 / 500000000)) (hi := (544320843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1103 / 640) = 1/(640 / 1103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (272160421 / 500000000) (544320843 / 1000000000) (Real.log (1103 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1103 / 640) = -Real.log (640 / 1103) := by
    rw [show ((1103 / 640) : ℝ) = ((640 / 1103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1285318443 / 1000000000) ≤ -Real.log (177 / 640) ∧
    -Real.log (177 / 640) ≤ (257063689 / 200000000) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 177) = 1/(177 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-257063689 / 200000000) (-1285318443 / 1000000000) (Real.log (177 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (211385251 / 500000000) ≤ -Real.log (125000 / 190773) ∧
    -Real.log (125000 / 190773) ≤ (422770503 / 1000000000) := by
  have h := checkLog_sound (w := (65773 / 315773)) (n := 12)
    (lo := (211385251 / 500000000)) (hi := (422770503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190773 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190773 / 125000) = 1/(125000 / 190773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (211385251 / 500000000) (422770503 / 1000000000) (Real.log (190773 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (190773 / 125000) = -Real.log (125000 / 190773) := by
    rw [show ((190773 / 125000) : ℝ) = ((125000 / 190773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (746936217 / 1000000000) ≤ -Real.log (59227 / 125000) ∧
    -Real.log (59227 / 125000) ≤ (746936219 / 1000000000) := by
  have h := checkLog_sound (w := (3273 / 121727)) (n := 12)
    (lo := (53789037 / 1000000000)) (hi := (26894519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 59227) = 1/(59227 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-746936219 / 1000000000) (-746936217 / 1000000000) (Real.log (59227 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3391777 / 8000000) ≤ -Real.log (1000000 / 1528019) ∧
    -Real.log (1000000 / 1528019) ≤ (211986063 / 500000000) := by
  have h := checkLog_sound (w := (528019 / 2528019)) (n := 12)
    (lo := (3391777 / 8000000)) (hi := (211986063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1528019 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1528019 / 1000000) = 1/(1000000 / 1528019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3391777 / 8000000) (211986063 / 500000000) (Real.log (1528019 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1528019 / 1000000) = -Real.log (1000000 / 1528019) := by
    rw [show ((1528019 / 1000000) : ℝ) = ((1000000 / 1528019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (750816547 / 1000000000) ≤ -Real.log (471981 / 1000000) ∧
    -Real.log (471981 / 1000000) ≤ (750816549 / 1000000000) := by
  have h := checkLog_sound (w := (28019 / 971981)) (n := 12)
    (lo := (57669367 / 1000000000)) (hi := (7208671 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 471981) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 471981) = 1/(471981 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-750816549 / 1000000000) (-750816547 / 1000000000) (Real.log (471981 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67694333 / 200000000) ≤ -Real.log (500000 / 701401) ∧
    -Real.log (500000 / 701401) ≤ (169235833 / 500000000) := by
  have h := checkLog_sound (w := (201401 / 1201401)) (n := 12)
    (lo := (67694333 / 200000000)) (hi := (169235833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701401 / 500000) = 1/(500000 / 701401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67694333 / 200000000) (169235833 / 500000000) (Real.log (701401 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (701401 / 500000) = -Real.log (500000 / 701401) := by
    rw [show ((701401 / 500000) : ℝ) = ((500000 / 701401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (257753281 / 500000000) ≤ -Real.log (298599 / 500000) ∧
    -Real.log (298599 / 500000) ≤ (515506563 / 1000000000) := by
  have h := checkLog_sound (w := (201401 / 798599)) (n := 12)
    (lo := (257753281 / 500000000)) (hi := (515506563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 298599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 298599) = 1/(298599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-515506563 / 1000000000) (-257753281 / 500000000) (Real.log (298599 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (169818611 / 500000000) ≤ -Real.log (500000 / 702219) ∧
    -Real.log (500000 / 702219) ≤ (339637223 / 1000000000) := by
  have h := checkLog_sound (w := (202219 / 1202219)) (n := 12)
    (lo := (169818611 / 500000000)) (hi := (339637223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702219 / 500000) = 1/(500000 / 702219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (169818611 / 500000000) (339637223 / 1000000000) (Real.log (702219 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (702219 / 500000) = -Real.log (500000 / 702219) := by
    rw [show ((702219 / 500000) : ℝ) = ((500000 / 702219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (518249781 / 1000000000) ≤ -Real.log (297781 / 500000) ∧
    -Real.log (297781 / 500000) ≤ (259124891 / 500000000) := by
  have h := checkLog_sound (w := (202219 / 797781)) (n := 12)
    (lo := (518249781 / 1000000000)) (hi := (259124891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 297781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 297781) = 1/(297781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-259124891 / 500000000) (-518249781 / 1000000000) (Real.log (297781 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (7310667 / 6250000) ≤ -Real.log (500000000000 / 1610523916457) ∧
    -Real.log (500000000000 / 1610523916457) ≤ (584853361 / 500000000) := by
  have h := checkLog_sound (w := (610523916457 / 2610523916457)) (n := 12)
    (lo := (23827977 / 50000000)) (hi := (476559541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1610523916457 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1610523916457 / 1000000000000) = 1/(500000000000 / 1610523916457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (7310667 / 6250000) (584853361 / 500000000) (Real.log (1610523916457 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1610523916457 / 500000000000) = -Real.log (500000000000 / 1610523916457) := by
    rw [show ((1610523916457 / 500000000000) : ℝ) = ((500000000000 / 1610523916457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1174788673 / 1000000000) ≤ -Real.log (500000000000 / 1618729355631) ∧
    -Real.log (500000000000 / 1618729355631) ≤ (46991547 / 40000000) := by
  have h := checkLog_sound (w := (618729355631 / 2618729355631)) (n := 12)
    (lo := (481641493 / 1000000000)) (hi := (240820747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1618729355631 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1618729355631 / 1000000000000) = 1/(500000000000 / 1618729355631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1174788673 / 1000000000) (46991547 / 40000000) (Real.log (1618729355631 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1618729355631 / 500000000000) = -Real.log (500000000000 / 1618729355631) := by
    rw [show ((1618729355631 / 500000000000) : ℝ) = ((500000000000 / 1618729355631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (426989113 / 500000000) ≤ -Real.log (500000000000 / 1174486518709) ∧
    -Real.log (500000000000 / 1174486518709) ≤ (213494557 / 250000000) := by
  have h := checkLog_sound (w := (174486518709 / 2174486518709)) (n := 12)
    (lo := (80415523 / 500000000)) (hi := (160831047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1174486518709 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1174486518709 / 1000000000000) = 1/(500000000000 / 1174486518709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (426989113 / 500000000) (213494557 / 250000000) (Real.log (1174486518709 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1174486518709 / 500000000000) = -Real.log (500000000000 / 1174486518709) := by
    rw [show ((1174486518709 / 500000000000) : ℝ) = ((500000000000 / 1174486518709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (857887003 / 1000000000) ≤ -Real.log (100000000000 / 235817261679) ∧
    -Real.log (100000000000 / 235817261679) ≤ (171577401 / 200000000) := by
  have h := checkLog_sound (w := (35817261679 / 435817261679)) (n := 12)
    (lo := (164739823 / 1000000000)) (hi := (10296239 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235817261679 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(235817261679 / 200000000000) = 1/(100000000000 / 235817261679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (857887003 / 1000000000) (171577401 / 200000000) (Real.log (235817261679 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (235817261679 / 100000000000) = -Real.log (100000000000 / 235817261679) := by
    rw [show ((235817261679 / 100000000000) : ℝ) = ((100000000000 / 235817261679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0128

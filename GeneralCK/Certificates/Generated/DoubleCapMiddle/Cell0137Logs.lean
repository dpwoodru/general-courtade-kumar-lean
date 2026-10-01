import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0137
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

theorem reflection_log_1_neg : (150919599 / 500000000) ≤ -Real.log (1280 / 1731) ∧
    -Real.log (1280 / 1731) ≤ (301839199 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 3011)) (n := 12)
    (lo := (150919599 / 500000000)) (hi := (301839199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1731 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1731 / 1280) = 1/(1280 / 1731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (150919599 / 500000000) (301839199 / 1000000000) (Real.log (1731 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1731 / 1280) = -Real.log (1280 / 1731) := by
    rw [show ((1731 / 1280) : ℝ) = ((1280 / 1731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (434395201 / 1000000000) ≤ -Real.log (829 / 1280) ∧
    -Real.log (829 / 1280) ≤ (217197601 / 500000000) := by
  have h := checkLog_sound (w := (451 / 2109)) (n := 12)
    (lo := (434395201 / 1000000000)) (hi := (217197601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 829) = 1/(829 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-217197601 / 500000000) (-434395201 / 1000000000) (Real.log (829 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (300972271 / 1000000000) ≤ -Real.log (2560 / 3459) ∧
    -Real.log (2560 / 3459) ≤ (18810767 / 62500000) := by
  have h := checkLog_sound (w := (899 / 6019)) (n := 12)
    (lo := (300972271 / 1000000000)) (hi := (18810767 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3459 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3459 / 2560) = 1/(2560 / 3459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (300972271 / 1000000000) (18810767 / 62500000) (Real.log (3459 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3459 / 2560) = -Real.log (2560 / 3459) := by
    rw [show ((3459 / 2560) : ℝ) = ((2560 / 3459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (432587427 / 1000000000) ≤ -Real.log (1661 / 2560) ∧
    -Real.log (1661 / 2560) ≤ (108146857 / 250000000) := by
  have h := checkLog_sound (w := (899 / 4221)) (n := 12)
    (lo := (432587427 / 1000000000)) (hi := (108146857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1661) = 1/(1661 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-108146857 / 250000000) (-432587427 / 1000000000) (Real.log (1661 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (533381809 / 1000000000) ≤ -Real.log (640 / 1091) ∧
    -Real.log (640 / 1091) ≤ (53338181 / 100000000) := by
  have h := checkLog_sound (w := (451 / 1731)) (n := 12)
    (lo := (533381809 / 1000000000)) (hi := (53338181 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091 / 640) = 1/(640 / 1091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (533381809 / 1000000000) (53338181 / 100000000) (Real.log (1091 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1091 / 640) = -Real.log (640 / 1091) := by
    rw [show ((1091 / 640) : ℝ) = ((640 / 1091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (30493029 / 25000000) ≤ -Real.log (189 / 640) ∧
    -Real.log (189 / 640) ≤ (609860581 / 500000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 189) = 1/(189 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-609860581 / 500000000) (-30493029 / 25000000) (Real.log (189 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (266002989 / 500000000) ≤ -Real.log (1280 / 2179) ∧
    -Real.log (1280 / 2179) ≤ (532005979 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 3459)) (n := 12)
    (lo := (266002989 / 500000000)) (hi := (532005979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2179 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2179 / 1280) = 1/(1280 / 2179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (266002989 / 500000000) (532005979 / 1000000000) (Real.log (2179 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2179 / 1280) = -Real.log (1280 / 2179) := by
    rw [show ((2179 / 1280) : ℝ) = ((1280 / 2179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1211815981 / 1000000000) ≤ -Real.log (381 / 1280) ∧
    -Real.log (381 / 1280) ≤ (1211815983 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1021)) (n := 12)
    (lo := (518668801 / 1000000000)) (hi := (259334401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 381) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 381) = 1/(381 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1211815983 / 1000000000) (-1211815981 / 1000000000) (Real.log (381 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (321837 / 781250) ≤ -Real.log (1000000 / 1509761) ∧
    -Real.log (1000000 / 1509761) ≤ (411951361 / 1000000000) := by
  have h := checkLog_sound (w := (509761 / 2509761)) (n := 12)
    (lo := (321837 / 781250)) (hi := (411951361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1509761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1509761 / 1000000) = 1/(1000000 / 1509761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (321837 / 781250) (411951361 / 1000000000) (Real.log (1509761 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1509761 / 1000000) = -Real.log (1000000 / 1509761) := by
    rw [show ((1509761 / 1000000) : ℝ) = ((1000000 / 1509761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (712862251 / 1000000000) ≤ -Real.log (490239 / 1000000) ∧
    -Real.log (490239 / 1000000) ≤ (712862253 / 1000000000) := by
  have h := checkLog_sound (w := (9761 / 990239)) (n := 12)
    (lo := (19715071 / 1000000000)) (hi := (38506 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 490239) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 490239) = 1/(490239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-712862253 / 1000000000) (-712862251 / 1000000000) (Real.log (490239 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (413155461 / 1000000000) ≤ -Real.log (50000 / 75579) ∧
    -Real.log (50000 / 75579) ≤ (206577731 / 500000000) := by
  have h := checkLog_sound (w := (25579 / 125579)) (n := 12)
    (lo := (413155461 / 1000000000)) (hi := (206577731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75579 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75579 / 50000) = 1/(50000 / 75579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (413155461 / 1000000000) (206577731 / 500000000) (Real.log (75579 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (75579 / 50000) = -Real.log (50000 / 75579) := by
    rw [show ((75579 / 50000) : ℝ) = ((50000 / 75579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (358289793 / 500000000) ≤ -Real.log (24421 / 50000) ∧
    -Real.log (24421 / 50000) ≤ (179144897 / 250000000) := by
  have h := checkLog_sound (w := (579 / 49421)) (n := 12)
    (lo := (11716203 / 500000000)) (hi := (23432407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24421) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 24421) = 1/(24421 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-179144897 / 250000000) (-358289793 / 500000000) (Real.log (24421 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (328061969 / 1000000000) ≤ -Real.log (40000 / 55531) ∧
    -Real.log (40000 / 55531) ≤ (32806197 / 100000000) := by
  have h := checkLog_sound (w := (15531 / 95531)) (n := 12)
    (lo := (328061969 / 1000000000)) (hi := (32806197 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55531 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55531 / 40000) = 1/(40000 / 55531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (328061969 / 1000000000) (32806197 / 100000000) (Real.log (55531 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (55531 / 40000) = -Real.log (40000 / 55531) := by
    rw [show ((55531 / 40000) : ℝ) = ((40000 / 55531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (491472443 / 1000000000) ≤ -Real.log (24469 / 40000) ∧
    -Real.log (24469 / 40000) ≤ (122868111 / 250000000) := by
  have h := checkLog_sound (w := (15531 / 64469)) (n := 12)
    (lo := (491472443 / 1000000000)) (hi := (122868111 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 24469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 24469) = 1/(24469 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-122868111 / 250000000) (-491472443 / 1000000000) (Real.log (24469 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (65842619 / 200000000) ≤ -Real.log (500000 / 694937) ∧
    -Real.log (500000 / 694937) ≤ (41151637 / 125000000) := by
  have h := checkLog_sound (w := (194937 / 1194937)) (n := 12)
    (lo := (65842619 / 200000000)) (hi := (41151637 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694937 / 500000) = 1/(500000 / 694937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (65842619 / 200000000) (41151637 / 125000000) (Real.log (694937 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (694937 / 500000) = -Real.log (500000 / 694937) := by
    rw [show ((694937 / 500000) : ℝ) = ((500000 / 694937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (98817957 / 200000000) ≤ -Real.log (305063 / 500000) ∧
    -Real.log (305063 / 500000) ≤ (247044893 / 500000000) := by
  have h := checkLog_sound (w := (194937 / 805063)) (n := 12)
    (lo := (98817957 / 200000000)) (hi := (247044893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 305063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 305063) = 1/(305063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-247044893 / 500000000) (-98817957 / 200000000) (Real.log (305063 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1124813611 / 1000000000) ≤ -Real.log (250000000000 / 769910696619) ∧
    -Real.log (250000000000 / 769910696619) ≤ (1124813613 / 1000000000) := by
  have h := checkLog_sound (w := (269910696619 / 1269910696619)) (n := 12)
    (lo := (431666431 / 1000000000)) (hi := (1686197 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769910696619 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(769910696619 / 500000000000) = 1/(250000000000 / 769910696619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1124813611 / 1000000000) (1124813613 / 1000000000) (Real.log (769910696619 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (769910696619 / 250000000000) = -Real.log (250000000000 / 769910696619) := by
    rw [show ((769910696619 / 250000000000) : ℝ) = ((250000000000 / 769910696619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (141216881 / 125000000) ≤ -Real.log (500000000000 / 1547418205643) ∧
    -Real.log (500000000000 / 1547418205643) ≤ (22594701 / 20000000) := by
  have h := checkLog_sound (w := (547418205643 / 2547418205643)) (n := 12)
    (lo := (109146967 / 250000000)) (hi := (436587869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547418205643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1547418205643 / 1000000000000) = 1/(500000000000 / 1547418205643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (141216881 / 125000000) (22594701 / 20000000) (Real.log (1547418205643 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1547418205643 / 500000000000) = -Real.log (500000000000 / 1547418205643) := by
    rw [show ((1547418205643 / 500000000000) : ℝ) = ((500000000000 / 1547418205643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (204883603 / 250000000) ≤ -Real.log (500000000000 / 1134721484327) ∧
    -Real.log (500000000000 / 1134721484327) ≤ (409767207 / 500000000) := by
  have h := checkLog_sound (w := (134721484327 / 2134721484327)) (n := 12)
    (lo := (3949601 / 31250000)) (hi := (126387233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134721484327 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1134721484327 / 1000000000000) = 1/(500000000000 / 1134721484327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (204883603 / 250000000) (409767207 / 500000000) (Real.log (1134721484327 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1134721484327 / 500000000000) = -Real.log (500000000000 / 1134721484327) := by
    rw [show ((1134721484327 / 500000000000) : ℝ) = ((500000000000 / 1134721484327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (5145643 / 6250000) ≤ -Real.log (250000000000 / 569502856787) ∧
    -Real.log (250000000000 / 569502856787) ≤ (411651441 / 500000000) := by
  have h := checkLog_sound (w := (69502856787 / 1069502856787)) (n := 12)
    (lo := (1301557 / 10000000)) (hi := (130155701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569502856787 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(569502856787 / 500000000000) = 1/(250000000000 / 569502856787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (5145643 / 6250000) (411651441 / 500000000) (Real.log (569502856787 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (569502856787 / 250000000000) = -Real.log (250000000000 / 569502856787) := by
    rw [show ((569502856787 / 250000000000) : ℝ) = ((250000000000 / 569502856787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0137
